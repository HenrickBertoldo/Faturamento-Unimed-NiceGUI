# ==========================================================================
# VALIDADOR TISS — Versão NiceGUI (migrada do Streamlit)
# ==========================================================================
# Reaproveita, sem nenhuma alteração de lógica, as mesmas funções de
# negócio já validadas na versão Streamlit (processar_xml_tiss, cálculo
# oficial de hash da ANS, todas as regras de correção). A camada de
# interface foi refeita do zero em NiceGUI.
#
# Arquivos necessários na MESMA pasta deste script:
#   - credentials.json  -> chave de Service Account do Google (somente
#                           LEITURA — a edição das regras foi retirada do
#                           app de propósito; quem precisa alterar uma regra
#                           faz isso direto na planilha, com acesso de
#                           Editor nela. A credencial deste app só precisa
#                           de permissão de Leitor na planilha.)
#   - config.json        -> {"spreadsheet_url": "https://docs.google.com/spreadsheets/d/SEU_ID/edit"}
#
# Como rodar localmente:
#   pip install nicegui pandas gspread google-auth
#   python app_unimed_nicegui.py
#
# Para publicar para outras pessoas acessarem, veja o GUIA_DEPLOY.md.
# ==========================================================================
import os
import re
import io
import json
import html
import hashlib
import zipfile
import difflib
import secrets
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta

import pandas as pd
import gspread
from google.oauth2.service_account import Credentials
from nicegui import ui, app

# ==========================================
# NAMESPACES E HELPERS TISS (idêntico à versão Streamlit)
# ==========================================
NS = {'ans': 'http://www.ans.gov.br/padroes/tiss/schemas'}
# Registra o prefixo 'ans' globalmente no ElementTree. Sem isso, ao reescrever
# o XML, o ElementTree ignora o prefixo original do documento e gera um
# genérico (ns0, ns1...) para qualquer namespace que encontrar — o conteúdo
# fica correto, mas o texto do arquivo muda de <ans:...> para <ns0:...>.
ET.register_namespace('ans', NS['ans'])

def ans_tag(tag_name): return f"{{{NS['ans']}}}{tag_name}"

def tag_limpa(element): return element.tag.split('}')[-1] if '}' in element.tag else element.tag

def indice_apos(parent, elem_ref):
    if elem_ref is None:
        return len(list(parent))
    return list(parent).index(elem_ref) + 1

def limpar_numero(valor):
    v = str(valor).strip()
    if v.lower() in ['nan', 'none', '<na>', '']: return ''
    if v.endswith('.00'): v = v[:-3]
    elif v.endswith('.0'): v = v[:-2]
    return v

def identificar_plano_pela_carteira(numero_carteira):
    """Identifica o plano do beneficiário a partir do início/prefixo da
    carteirinha. Reaproveita o MESMO tamanho de prefixo (4 dígitos) que a
    aplicação já usa para reconhecer a Unimed 0014 (ver 'eh_unimed_0014' em
    processar_xml_tiss) — não inventa um novo tamanho de prefixo nem uma
    nova regra de identificação, apenas generaliza a lógica existente para
    também poder ser comparada com uma lista de planos contratados."""
    return (numero_carteira or '')[:4]

def padronizar_codigo_8_digitos(cod):
    """Garante 8 dígitos num código totalmente numérico, repondo à esquerda
    quantos zeros forem necessários. Isso importa porque, quando uma célula
    do Google Sheets é interpretada como número (em vez de texto), TODOS os
    zeros à esquerda são descartados — não só um. Um código como '00146803'
    (dois zeros à esquerda) vira '146803' na planilha; a versão antiga desta
    função só sabia repor exatamente 1 zero (caso de 7 dígitos), então um
    código que perdeu 2 zeros ou mais nunca voltava a bater com o mesmo
    código extraído do XML, e a substituição na tabela 'itens' (ou em
    qualquer outra tabela que use códigos de 8 dígitos) ficava sem efeito
    silenciosamente."""
    c = limpar_numero(cod)
    return c.zfill(8) if c.isdigit() and len(c) < 8 else c


# ==========================================
# ESTRUTURA PADRÃO DAS TABELAS DE REGRAS (idêntico à versão Streamlit)
# ==========================================
tabelas_padrao = {
    'troca_equipe_sadt': pd.DataFrame(columns=['Nome Original (Erro)', 'Nome Novo', 'CRM Novo', 'CBO Novo', 'Cód Operadora Novo', 'Grau Part Novo', 'Conselho Novo', 'UF Nova']),
    'medicos': pd.DataFrame(columns=['Nome do Médico', 'CBO Correto', 'Substituir por Cód. Operadora', 'Código na Operadora']),
    'procedimentos': pd.DataFrame(columns=['Código do Procedimento', 'Grau Part Obrigatório', 'Via de Acesso (1, 2 ou EXCLUIR)', 'Técnica (1, 2 ou EXCLUIR)']),
    'conveniados': pd.DataFrame(columns=['Nome do Médico Conveniado']),
    'blindagem': pd.DataFrame(columns=['Código Prestador Protegido', 'Tipo', 'Código']),
    'itens': pd.DataFrame(columns=['Código Incorreto', 'Código Correto']),
    'unidades': pd.DataFrame(columns=['Código do Item', 'Unidade de Medida Correta']),
    'anvisa': pd.DataFrame(columns=['Código do Item', 'Registro ANVISA', 'Ref. Fabricante'])
}

def formatar_tabela_padrao(df):
    for col in df.columns:
        df[col] = df[col].astype(str).str.strip().str.upper()
        df[col] = df[col].replace(['NAN', 'NONE', '<NA>'], '')
        col_upper = col.upper()
        if any(k in col_upper for k in ['CONSELHO', 'UF', 'GRAU PART', 'VIA DE ACESSO', 'TÉCNICA']):
            df[col] = df[col].apply(lambda x: x.zfill(2) if (x.isdigit() and len(x) == 1) else x)
    return df


# ==========================================
# ACESSO AO GOOGLE SHEETS (somente LEITURA, via Service Account)
# A edição das regras de negócio foi retirada do app de propósito: como o
# app é usado por várias pessoas, mas só algumas devem poder alterar as
# regras, a edição fica restrita à própria planilha do Google Sheets
# (acesso de Editor lá, gerenciado separadamente). Isto aqui só LÊ as
# regras mais recentes a cada carregamento da página — nunca escreve nelas.
# Substitui o st.connection("gsheets", ...) do Streamlit — aqui a app não
# roda dentro do Streamlit, então falamos com a planilha diretamente via
# gspread. Se as credenciais não estiverem configuradas, a aplicação
# continua funcionando normalmente, só sem nenhuma regra pré-carregada
# (você recebe um aviso, não um erro fatal).
# ==========================================
PASTA_SCRIPT = os.path.dirname(os.path.abspath(__file__))
CREDENCIAIS_PATH = os.path.join(PASTA_SCRIPT, "credentials.json")
CONFIG_PATH = os.path.join(PASTA_SCRIPT, "config.json")
# Escopo só de leitura — a credencial deste app não consegue gravar na
# planilha mesmo que algum código tente (não que exista mais código que
# tente, mas é uma camada extra de segurança independente do código).
_SCOPES_SHEETS = ["https://www.googleapis.com/auth/spreadsheets.readonly"]

def _carregar_credenciais_service_account():
    """Procura a credencial do Google nesta ordem (cobre os 3 jeitos mais
    comuns de rodar esta aplicação):
    1. Variável de ambiente GOOGLE_CREDENTIALS_JSON — contendo o JSON inteiro
       da chave (usada em plataformas como Hugging Face Spaces);
    2. Secret File do Render, sempre montado em /etc/secrets/credentials.json;
    3. Arquivo credentials.json na mesma pasta deste script (uso local, no
       seu computador).
    Retorna (credentials_ou_None, mensagem_de_erro_ou_None)."""
    conteudo_env = os.environ.get("GOOGLE_CREDENTIALS_JSON")
    if conteudo_env:
        try:
            info = json.loads(conteudo_env)
            return Credentials.from_service_account_info(info, scopes=_SCOPES_SHEETS), None
        except Exception as e:
            return None, f"Variável de ambiente GOOGLE_CREDENTIALS_JSON inválida: {e}"

    for caminho in ["/etc/secrets/credentials.json", CREDENCIAIS_PATH]:
        if os.path.isfile(caminho):
            try:
                return Credentials.from_service_account_file(caminho, scopes=_SCOPES_SHEETS), None
            except Exception as e:
                return None, f"Falha ao ler credenciais em {caminho}: {e}"

    return None, ("Nenhuma credencial do Google encontrada. Configure a variável de ambiente "
                   "GOOGLE_CREDENTIALS_JSON, ou um Secret File 'credentials.json' (Render), ou "
                   "coloque um arquivo credentials.json na pasta da aplicação (uso local).")

def _obter_spreadsheet_url():
    """Procura o link da planilha nesta ordem: variável de ambiente
    SPREADSHEET_URL, depois o arquivo config.json local."""
    url_env = os.environ.get("SPREADSHEET_URL")
    if url_env:
        return url_env, None
    if os.path.isfile(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, encoding='utf-8') as f:
                return json.load(f)['spreadsheet_url'], None
        except Exception as e:
            return None, f"Falha ao ler config.json: {e}"
    return None, "Defina a variável de ambiente SPREADSHEET_URL, ou crie um config.json na pasta da aplicação."

def _conectar_planilha():
    """Retorna o objeto da planilha (gspread Spreadsheet), ou None se as
    credenciais/config ainda não foram configuradas ou a conexão falhar."""
    creds, erro_cred = _carregar_credenciais_service_account()
    if creds is None:
        return None, erro_cred
    url, erro_url = _obter_spreadsheet_url()
    if url is None:
        return None, erro_url
    try:
        gc = gspread.authorize(creds)
        sh = gc.open_by_url(url) if url.startswith('http') else gc.open_by_key(url)
        return sh, None
    except Exception as e:
        return None, str(e)

def carregar_tabelas_do_sheets():
    """Busca a versão mais recente de todas as tabelas de regras no Google
    Sheets. Se a conexão não estiver configurada ou falhar, devolve as
    tabelas padrão (vazias) — a aplicação continua funcionando, só sem
    regra nenhuma pré-carregada até isso ser corrigido."""
    sh, erro_conexao = _conectar_planilha()
    dfs = {}
    avisos = []
    if erro_conexao:
        avisos.append(f"Não foi possível conectar ao Google Sheets: {erro_conexao}")
    for aba in tabelas_padrao.keys():
        df = tabelas_padrao[aba].copy()
        if sh is not None:
            try:
                ws = sh.worksheet(aba)
                registros = ws.get_all_records()
                if registros:
                    df = pd.DataFrame(registros)
                    for col in df.columns:
                        df[col] = df[col].astype(str).apply(limpar_numero)
                    df = formatar_tabela_padrao(df)
            except Exception as e:
                avisos.append(f"Aba '{aba}': {e}")
        dfs[aba] = df
    return dfs, avisos


# ==========================================
# MOTOR DE CORREÇÃO — CÓPIA FIEL da versão Streamlit (nenhuma regra alterada)
# ==========================================
def calcular_tempo_oxigenio(hora_ini_str, qtd_executada, tipo_unidade):
    try:
        qtd = float(qtd_executada.strip())
        # Regra especial: quantidade executada = 24 (horas) -> dia inteiro (00:00:00 às 23:59:59)
        if tipo_unidade == '60034335' and qtd == 24:
            return "00:00:00", "23:59:59", True
        t_ini = datetime.strptime(hora_ini_str.strip(), "%H:%M:%S")
        if tipo_unidade == '60034335': return hora_ini_str, (t_ini + timedelta(hours=qtd)).strftime("%H:%M:%S"), True
        elif tipo_unidade == '60034343': return hora_ini_str, (t_ini + timedelta(minutes=qtd)).strftime("%H:%M:%S"), True
        return hora_ini_str, hora_ini_str, True
    except (ValueError, AttributeError, TypeError):
        return hora_ini_str, hora_ini_str, False

def reordenar_servico_executado(servicos_node, nova_anvisa=None, nova_ref=None):
    valores = {tag_limpa(c): c for c in list(servicos_node)}
    servicos_node.clear()
    ordem_tiss = ['dataExecucao', 'horaInicial', 'horaFinal', 'codigoTabela', 'codigoProcedimento',
                  'quantidadeExecutada', 'unidadeMedida', 'reducaoAcrescimo', 'valorUnitario', 'valorTotal',
                  'descricaoProcedimento', 'registroANVISA', 'codigoRefFabricante']
    for tag in ordem_tiss:
        if tag == 'registroANVISA' and nova_anvisa:
            el = ET.Element(ans_tag('registroANVISA'))
            el.text = nova_anvisa
            servicos_node.append(el)
        elif tag == 'codigoRefFabricante' and nova_ref:
            el = ET.Element(ans_tag('codigoRefFabricante'))
            el.text = nova_ref
            servicos_node.append(el)
        elif tag in valores:
            if tag == 'registroANVISA' and (not valores[tag].text or not valores[tag].text.strip()) and nova_anvisa: valores[tag].text = nova_anvisa
            if tag == 'codigoRefFabricante' and (not valores[tag].text or not valores[tag].text.strip()) and nova_ref: valores[tag].text = nova_ref
            servicos_node.append(valores[tag])

def corrigir_valores_negativos(root, auditoria):
    logs = []
    for elem in root.iter():
        tag_nome = elem.tag.split('}')[-1] if '}' in elem.tag else elem.tag
        if tag_nome in ['quantidadeExecutada', 'valorTotal'] and elem.text:
            texto_original = elem.text.strip()
            if texto_original.startswith('-'):
                texto_corrigido = texto_original.lstrip('-')
                elem.text = texto_corrigido
                logs.append(f"Tag <{tag_nome}>: {texto_original} ➔ {texto_corrigido}")
    
    if 'valores_negativos' not in auditoria:
        auditoria['valores_negativos'] = []
    auditoria['valores_negativos'].extend(logs)
    return len(logs)

def corrigir_motivo_encerramento(root, auditoria):
    logs = []
    for elem in root.iter():
        tag_nome = elem.tag.split('}')[-1] if '}' in elem.tag else elem.tag
        if tag_nome == 'motivoEncerramento' and elem.text:
            if elem.text.strip() == '11':
                elem.text = '12'
                logs.append("Tag <motivoEncerramento>: 11 ➔ 12")
    
    if 'motivo_encerramento' not in auditoria:
        auditoria['motivo_encerramento'] = []
    auditoria['motivo_encerramento'].extend(logs)
    return len(logs)

def _somar_segundos(hora_str, segundos):
    """Soma 'segundos' a um horário HH:MM:SS, com rollover natural de minuto/hora
    (ex: 23:59:59 + 2s = 00:00:01)."""
    t = datetime.strptime(hora_str.strip(), "%H:%M:%S")
    return (t + timedelta(seconds=segundos)).strftime("%H:%M:%S")

def ajustar_horarios_duplicados(procs_container, auditoria):
    """🆕 NOVA REGRA: quando um procedimento é dividido em vários itens de
    quantidadeExecutada=1 (em vez de um único item com quantidade > 1), a
    Unimed rejeita a guia com a crítica "Serviço duplicado" sempre que dois
    ou mais itens têm o mesmo código de procedimento, a mesma data e o mesmo
    horário inicial/final. Esta regra detecta esses grupos e escalona os
    horários em +1s, +2s, +3s... a partir do segundo item do grupo (o
    primeiro item permanece intacto), sem alterar quantidade, valor ou
    qualquer outro dado do procedimento."""
    if 'horarios_duplicados' not in auditoria:
        auditoria['horarios_duplicados'] = []

    grupos = {}
    for proc_exec in procs_container.findall('ans:procedimentoExecutado', NS):
        cod_elem = proc_exec.find('.//ans:codigoProcedimento', NS)
        data_elem = proc_exec.find('ans:dataExecucao', NS)
        h_ini_elem = proc_exec.find('ans:horaInicial', NS)
        h_fim_elem = proc_exec.find('ans:horaFinal', NS)
        if cod_elem is None or data_elem is None or h_ini_elem is None or h_fim_elem is None:
            continue
        if not (cod_elem.text and data_elem.text and h_ini_elem.text and h_fim_elem.text):
            continue
        chave = (padronizar_codigo_8_digitos(cod_elem.text), data_elem.text.strip(), h_ini_elem.text.strip(), h_fim_elem.text.strip())
        grupos.setdefault(chave, []).append((h_ini_elem, h_fim_elem))

    for (cod_p, data_exec, h_ini_orig, h_fim_orig), ocorrencias in grupos.items():
        if len(ocorrencias) < 2:
            continue
        for i, (h_ini_elem, h_fim_elem) in enumerate(ocorrencias[1:], start=1):
            h_ini_elem.text = _somar_segundos(h_ini_orig, i)
            h_fim_elem.text = _somar_segundos(h_fim_orig, i)
        auditoria['horarios_duplicados'].append(
            f"Procedimento {cod_p} em {data_exec}: {len(ocorrencias)} ocorrências no horário {h_ini_orig} "
            f"— {len(ocorrencias) - 1} escalonada(s) em +1s, +2s... para evitar crítica 'Serviço duplicado'."
        )

def calcular_hash_tiss(root, hash_node):
    """🛠️ ALGORITMO OFICIAL DA ANS para o hash do Padrão TISS (confirmado com a
    Unimed/Validador TISS): NÃO é o MD5 dos bytes do arquivo inteiro — é o MD5
    da CONCATENAÇÃO do conteúdo (sem as tags) de todos os elementos-folha, na
    ordem em que aparecem no documento, usando ISO-8859-1. Tags vazias, ou que
    só contêm espaço/tab/quebra de linha, não entram no cálculo. Como o cálculo
    não depende de nenhum detalhe de formatação/serialização do XML (tags
    autofechadas, indentação, quebra de linha), ele é imune ao tipo de
    divergência de bytes que causava os erros "Hash inválido" na importação."""
    partes = []
    for elem in root.iter():
        if elem is hash_node:
            continue  # o próprio hash é sempre tratado como vazio no cálculo
        if len(list(elem)) > 0:
            continue  # só elementos-folha (sem filhos) contam
        texto = elem.text
        if texto is None or texto.strip() == '':
            continue  # tags vazias ou só com espaço/tab/quebra de linha não contam
        partes.append(texto)
    concatenado = ''.join(partes)
    return hashlib.md5(concatenado.encode('ISO-8859-1')).hexdigest()

def recalcular_hash_e_serializar(tree, root):
    """Recebe uma árvore ElementTree já com os dados finais e devolve os bytes
    prontos para gravação: recalcula o hash (algoritmo oficial ANS) e serializa
    em ISO-8859-1 com quebras de linha CRLF. Usada tanto pelo motor automático
    (processar_xml_tiss) quanto pelo salvamento manual no editor de XML —
    garante que os dois caminhos gerem hash de forma idêntica."""
    hash_node = root.find('.//ans:hash', NS)
    if hash_node is not None:
        hash_node.text = ""
        md5_hash = calcular_hash_tiss(root, hash_node)
        hash_node.text = md5_hash

    temp_buffer = io.BytesIO()
    tree.write(temp_buffer, encoding='ISO-8859-1', xml_declaration=True)
    xml_bytes = temp_buffer.getvalue()
    xml_bytes = xml_bytes.replace(b"<?xml version='1.0' encoding='ISO-8859-1'?>", b'<?xml version="1.0" encoding="ISO-8859-1"?>')
    xml_bytes = xml_bytes.replace(b'\r\n', b'\n').replace(b'\n', b'\r\n')
    return xml_bytes

def _extrair_hash_do_texto(texto):
    """Extrai o valor atualmente escrito dentro de <ans:hash>...</ans:hash> a
    partir do texto bruto (via regex, não exige XML bem formado — útil para
    exibir o hash mesmo enquanto o usuário está editando o XML no meio do
    processo, antes de salvar)."""
    m = re.search(r'<ans:hash>([^<]*)</ans:hash>', texto)
    return m.group(1).strip() if m else None

def validar_e_recalcular_xml_editado(texto_editado):
    """Usada pelo editor manual (Salvar alterações / Localizar e Substituir).
    Tenta interpretar o texto do editor como XML válido e, se conseguir,
    recalcula o hash com a MESMA função usada pelo motor automático.
    Retorna (xml_bytes_ou_None, mensagem_de_erro_ou_None)."""
    try:
        xml_encodado = texto_editado.encode('ISO-8859-1')
    except UnicodeEncodeError as e:
        return None, f"O texto contém um caractere fora do padrão ISO-8859-1 (posição {e.start}: '{texto_editado[e.start:e.start+1]}'). Remova ou substitua esse caractere antes de salvar."

    try:
        root = ET.fromstring(xml_encodado)
    except ET.ParseError as e:
        return None, f"XML inválido — não é possível salvar: {e}"

    tree = ET.ElementTree(root)
    try:
        xml_bytes = recalcular_hash_e_serializar(tree, root)
    except Exception as e:
        return None, f"Falha ao recalcular o hash/serializar o XML: {e}"
    return xml_bytes, None

# ==========================================================================
# 🆕 FRAGMENTAÇÃO DE PROCEDIMENTOS PARA OUTRO PRESTADOR (ex.: 220163)
# ==========================================================================
# Constantes fixas do hospital/UMC contratante (código 110591) usadas quando
# o valor não está disponível na própria guia de origem. Este aplicativo já
# atende especificamente a este hospital em outras regras (ex.: prefixo de
# carteirinha '0014' da Unimed), então fixar esses dois valores aqui segue a
# mesma convenção — ajuste-os se o nome/registro oficial mudar.
_CODIGO_HOSPITAL_UMC = '110591'
_NOME_HOSPITAL_UMC = 'COMPLEXO HOSPITALAR UBERLANDIA SA - UMC'

def _texto_de(pai, caminho):
    """Busca um elemento pelo caminho XPath (namespace 'ans') e devolve seu
    texto, ou None se o elemento não existir ou estiver vazio."""
    if pai is None:
        return None
    elem = pai.find(caminho, NS)
    return elem.text if elem is not None and elem.text else None

def _adicionar_procedimento_realizado(procs_realizados_pai, proc_exec_origem, prestador_frag, sequencial):
    """Copia um procedimentoExecutado (modelo de guiaResumoInternacao) para
    um procedimentoRealizado (modelo de guiaHonorarios), remapeando os nomes
    de campo conforme o XML de referência do fragmento 220163. Devolve o
    valorTotal do item, para acumular o total de honorários da guia."""
    pr = ET.SubElement(procs_realizados_pai, ans_tag('procedimentoRealizado'))

    ET.SubElement(pr, ans_tag('sequencialItem')).text = _texto_de(proc_exec_origem, 'ans:sequencialItem') or str(sequencial)
    for campo in ('dataExecucao', 'horaInicial', 'horaFinal'):
        valor = _texto_de(proc_exec_origem, f'ans:{campo}')
        if valor: ET.SubElement(pr, ans_tag(campo)).text = valor

    proc_origem = proc_exec_origem.find('ans:procedimento', NS)
    procedimento = ET.SubElement(pr, ans_tag('procedimento'))
    for campo in ('codigoTabela', 'codigoProcedimento', 'descricaoProcedimento'):
        valor = _texto_de(proc_origem, f'ans:{campo}')
        if valor: ET.SubElement(procedimento, ans_tag(campo)).text = valor

    for campo in ('quantidadeExecutada', 'viaAcesso', 'tecnicaUtilizada', 'reducaoAcrescimo', 'valorUnitario', 'valorTotal'):
        valor = _texto_de(proc_exec_origem, f'ans:{campo}')
        if valor: ET.SubElement(pr, ans_tag(campo)).text = valor

    # Profissionais do prestador fragmentado (identEquipe/identificacaoEquipe
    # ou equipeSadt na guia original ➔ profissionais no modelo de honorários).
    equipes = proc_exec_origem.findall('ans:identEquipe', NS) + proc_exec_origem.findall('ans:equipeSadt', NS)
    for eq in equipes:
        cod_prestador_eq = _texto_de(eq, './/ans:codProfissional/ans:codigoPrestadorNaOperadora')
        if cod_prestador_eq is None or limpar_numero(cod_prestador_eq) != prestador_frag:
            continue
        origem_eq = eq.find('ans:identificacaoEquipe', NS) if tag_limpa(eq) == 'identEquipe' else eq
        profissionais = ET.SubElement(pr, ans_tag('profissionais'))
        mapa_campos = [
            ('grauPart', 'grauParticipacao'), ('grauParticipacao', 'grauParticipacao'),
        ]
        grau = _texto_de(origem_eq, 'ans:grauPart') or _texto_de(origem_eq, 'ans:grauParticipacao')
        if grau: ET.SubElement(profissionais, ans_tag('grauParticipacao')).text = grau
        cod_prof = ET.SubElement(profissionais, ans_tag('codProfissional'))
        ET.SubElement(cod_prof, ans_tag('codigoPrestadorNaOperadora')).text = limpar_numero(cod_prestador_eq)
        nome_prof = _texto_de(origem_eq, 'ans:nomeProf') or _texto_de(origem_eq, 'ans:nomeProfissional')
        if nome_prof: ET.SubElement(profissionais, ans_tag('nomeProfissional')).text = nome_prof
        conselho = _texto_de(origem_eq, 'ans:conselho') or _texto_de(origem_eq, 'ans:conselhoProfissional')
        if conselho: ET.SubElement(profissionais, ans_tag('conselhoProfissional')).text = conselho
        num_conselho = _texto_de(origem_eq, 'ans:numeroConselhoProfissional')
        if num_conselho: ET.SubElement(profissionais, ans_tag('numeroConselhoProfissional')).text = num_conselho
        uf = _texto_de(origem_eq, 'ans:UF')
        if uf: ET.SubElement(profissionais, ans_tag('UF')).text = uf
        cbo = _texto_de(origem_eq, 'ans:CBOS') or _texto_de(origem_eq, 'ans:CBO') or _texto_de(origem_eq, 'ans:codigoCBOS') or _texto_de(origem_eq, 'ans:codigoCBO')
        if cbo: ET.SubElement(profissionais, ans_tag('CBO')).text = cbo

    try:
        return float(_texto_de(proc_exec_origem, 'ans:valorTotal') or 0)
    except ValueError:
        return 0.0

def _construir_guia_honorarios(guias_tiss_pai, guia_origem, prestador_frag, itens_guia, data_emissao):
    """Monta uma guiaHonorarios (modelo do XML de referência do fragmento
    220163) a partir de uma guiaResumoInternacao de origem e da lista de
    procedimentos que a regra de fragmentação decidiu mover para ela."""
    guia_hon = ET.SubElement(guias_tiss_pai, ans_tag('guiaHonorarios'))

    cab_guia = ET.SubElement(guia_hon, ans_tag('cabecalhoGuia'))
    registro_ans = _texto_de(guia_origem, './/ans:cabecalhoGuia/ans:registroANS')
    if registro_ans: ET.SubElement(cab_guia, ans_tag('registroANS')).text = registro_ans
    # Não há, na guia original, um "número de guia do prestador" próprio do
    # 220163 (essa numeração pertence ao sistema de faturamento dele, ao qual
    # esta aplicação não tem acesso). Reaproveitamos o número da guia
    # original em vez de inventar uma sequência nova — ajuste manualmente se
    # o prestador exigir sua própria numeração antes do envio.
    numero_guia_prestador = _texto_de(guia_origem, './/ans:cabecalhoGuia/ans:numeroGuiaPrestador')
    if numero_guia_prestador: ET.SubElement(cab_guia, ans_tag('numeroGuiaPrestador')).text = numero_guia_prestador

    numero_solicitacao = _texto_de(guia_origem, './/ans:numeroGuiaSolicitacaoInternacao')
    if numero_solicitacao: ET.SubElement(guia_hon, ans_tag('guiaSolicInternacao')).text = numero_solicitacao

    senha = _texto_de(guia_origem, './/ans:dadosAutorizacao/ans:senha')
    if senha: ET.SubElement(guia_hon, ans_tag('senha')).text = senha

    numero_guia_operadora = _texto_de(guia_origem, './/ans:dadosAutorizacao/ans:numeroGuiaOperadora')
    if numero_guia_operadora: ET.SubElement(guia_hon, ans_tag('numeroGuiaOperadora')).text = numero_guia_operadora

    beneficiario = ET.SubElement(guia_hon, ans_tag('beneficiario'))
    numero_carteira = _texto_de(guia_origem, './/ans:dadosBeneficiario/ans:numeroCarteira')
    if numero_carteira: ET.SubElement(beneficiario, ans_tag('numeroCarteira')).text = numero_carteira
    ET.SubElement(beneficiario, ans_tag('atendimentoRN')).text = _texto_de(guia_origem, './/ans:dadosBeneficiario/ans:atendimentoRN') or 'N'

    cnes_original = _texto_de(guia_origem, './/ans:dadosExecutante/ans:CNES')
    prestador_hospital = _texto_de(guia_origem, './/ans:dadosExecutante/ans:contratadoExecutante/ans:codigoPrestadorNaOperadora') or _CODIGO_HOSPITAL_UMC

    local_contratado = ET.SubElement(guia_hon, ans_tag('localContratado'))
    cod_contratado = ET.SubElement(local_contratado, ans_tag('codigoContratado'))
    ET.SubElement(cod_contratado, ans_tag('codigoNaOperadora')).text = prestador_hospital
    ET.SubElement(local_contratado, ans_tag('nomeContratado')).text = _NOME_HOSPITAL_UMC
    if cnes_original: ET.SubElement(local_contratado, ans_tag('cnes')).text = cnes_original

    contratado_exec = ET.SubElement(guia_hon, ans_tag('dadosContratadoExecutante'))
    ET.SubElement(contratado_exec, ans_tag('codigonaOperadora')).text = prestador_frag
    if cnes_original: ET.SubElement(contratado_exec, ans_tag('cnesContratadoExecutante')).text = cnes_original

    dados_internacao = ET.SubElement(guia_hon, ans_tag('dadosInternacao'))
    data_inicio = _texto_de(guia_origem, './/ans:dadosInternacao/ans:dataInicioFaturamento')
    if data_inicio: ET.SubElement(dados_internacao, ans_tag('dataInicioFaturamento')).text = data_inicio
    data_fim = _texto_de(guia_origem, './/ans:dadosInternacao/ans:dataFinalFaturamento')
    if data_fim: ET.SubElement(dados_internacao, ans_tag('dataFimFaturamento')).text = data_fim

    procs_realizados = ET.SubElement(guia_hon, ans_tag('procedimentosRealizados'))
    valor_total_honorarios = sum(
        _adicionar_procedimento_realizado(procs_realizados, item['proc_exec'], prestador_frag, i)
        for i, item in enumerate(itens_guia, start=1)
    )
    ET.SubElement(guia_hon, ans_tag('valorTotalHonorarios')).text = f"{valor_total_honorarios:.2f}"

    if data_emissao: ET.SubElement(guia_hon, ans_tag('dataEmissaoGuia')).text = data_emissao

def construir_fragmento_honorarios(root_original, prestador_frag, itens):
    """Monta um novo documento mensagemTISS (modelo de guiaHonorarios, igual
    ao XML de referência do fragmento 220163) contendo uma guiaHonorarios
    para cada guia de internação de origem que teve procedimento(s) movidos
    para este prestador. Reaproveita os identificadores já existentes na
    guia original (número de solicitação, senha, número da guia, CNES, lote
    e cabeçalho da transação) em vez de inventar uma numeração própria.
    Devolve (tree, root) prontos para passar por recalcular_hash_e_serializar
    — a mesma função usada pelo restante da aplicação."""
    cabecalho_original = root_original.find('.//ans:cabecalho', NS)
    lote_original = root_original.find('.//ans:loteGuias/ans:numeroLote', NS)
    data_emissao = _texto_de(cabecalho_original, './/ans:dataRegistroTransacao')

    root_frag = ET.Element(ans_tag('mensagemTISS'), dict(root_original.attrib))
    tree_frag = ET.ElementTree(root_frag)

    cabecalho = ET.SubElement(root_frag, ans_tag('cabecalho'))
    ident_transacao = ET.SubElement(cabecalho, ans_tag('identificacaoTransacao'))
    for campo in ('tipoTransacao', 'sequencialTransacao', 'dataRegistroTransacao', 'horaRegistroTransacao'):
        valor = _texto_de(cabecalho_original, f'.//ans:{campo}')
        if valor: ET.SubElement(ident_transacao, ans_tag(campo)).text = valor

    origem = ET.SubElement(cabecalho, ans_tag('origem'))
    ident_prestador = ET.SubElement(origem, ans_tag('identificacaoPrestador'))
    ET.SubElement(ident_prestador, ans_tag('codigoPrestadorNaOperadora')).text = prestador_frag

    destino = ET.SubElement(cabecalho, ans_tag('destino'))
    registro_ans_destino = _texto_de(cabecalho_original, './/ans:destino/ans:registroANS')
    if registro_ans_destino: ET.SubElement(destino, ans_tag('registroANS')).text = registro_ans_destino

    padrao = _texto_de(cabecalho_original, './/ans:Padrao')
    if padrao: ET.SubElement(cabecalho, ans_tag('Padrao')).text = padrao

    prestador_para_operadora = ET.SubElement(root_frag, ans_tag('prestadorParaOperadora'))
    lote_guias = ET.SubElement(prestador_para_operadora, ans_tag('loteGuias'))
    ET.SubElement(lote_guias, ans_tag('numeroLote')).text = (lote_original.text if lote_original is not None and lote_original.text else '')
    guias_tiss = ET.SubElement(lote_guias, ans_tag('guiasTISS'))

    # Agrupa por guia de origem: uma guiaHonorarios por internação de origem,
    # preservando o vínculo 1:1 mesmo que várias guias do mesmo arquivo
    # tenham itens elegíveis para este prestador.
    por_guia = {}
    for item in itens:
        grupo = por_guia.setdefault(id(item['guia']), {'guia': item['guia'], 'itens': []})
        grupo['itens'].append(item)

    for grupo in por_guia.values():
        _construir_guia_honorarios(guias_tiss, grupo['guia'], prestador_frag, grupo['itens'], data_emissao)

    epilogo = ET.SubElement(root_frag, ans_tag('epilogo'))
    ET.SubElement(epilogo, ans_tag('hash'))

    return tree_frag, root_frag

def processar_xml_tiss(arquivo_xml, dfs):
    auditoria = {
        'cbos': [], 'medicos_trocados': [], 'itens': [], 'anvisa': [], 'unidades': [], 'oxigenio': [],
        'conveniados_excluidos': [], 'procedimentos_ajustados': [], 'guias_blindadas': [], 'erros': [],
        'valores_negativos': [], 'motivo_encerramento': [], 'horarios_duplicados': [], 'fragmentados': []
    }
    
    arquivo_xml.seek(0)
    tree = ET.parse(arquivo_xml)
    root = tree.getroot()

    # 1. Regra de Valores Negativos
    corrigir_valores_negativos(root, auditoria)

    # 2. Regra do Motivo de Encerramento 11 ➔ 12
    corrigir_motivo_encerramento(root, auditoria)

    # 3. Carregamento das Tabelas e Dicionários
    df_medicos = dfs.get('medicos', pd.DataFrame()) if isinstance(dfs, dict) else pd.DataFrame()
    dict_medicos = {}
    if df_medicos is not None and not df_medicos.empty:
        for _, r in df_medicos.iterrows():
            nome = str(r.get('Nome do Médico', '')).strip().upper()
            if nome and nome not in ['NAN', 'NONE', '<NA>', '']:
                dict_medicos[nome] = r

    df_equipe_sadt = dfs.get('troca_equipe_sadt', pd.DataFrame()) if isinstance(dfs, dict) else pd.DataFrame()
    dict_equipe_sadt = {}
    if df_equipe_sadt is not None and not df_equipe_sadt.empty:
        for _, r in df_equipe_sadt.iterrows():
            orig = str(r.get('Nome Original (Erro)', '')).strip().upper()
            if orig and orig not in ['NAN', 'NONE', '<NA>', '']:
                dict_equipe_sadt[orig] = {
                    'nome_novo': str(r.get('Nome Novo', '')).strip(),
                    'crm_novo': limpar_numero(r.get('CRM Novo', '')),
                    'cbo_novo': limpar_numero(r.get('CBO Novo', '')),
                    'cod_op_novo': limpar_numero(r.get('Cód Operadora Novo', '')),
                    'grau_novo': limpar_numero(r.get('Grau Part Novo', '')),
                    'conselho_novo': limpar_numero(r.get('Conselho Novo', '')),
                    'uf_nova': limpar_numero(r.get('UF Nova', ''))
                }

    df_conveniados = dfs.get('conveniados', pd.DataFrame()) if isinstance(dfs, dict) else pd.DataFrame()
    set_conveniados = set(df_conveniados['Nome do Médico Conveniado'].dropna().astype(str).str.strip().str.upper()) if not df_conveniados.empty and 'Nome do Médico Conveniado' in df_conveniados.columns else set()

    df_blindagem = dfs.get('blindagem', pd.DataFrame()) if isinstance(dfs, dict) else pd.DataFrame()
    tem_colunas_fragmentacao = not df_blindagem.empty and 'Tipo' in df_blindagem.columns and 'Código' in df_blindagem.columns

    # Linhas de "proteção total" (comportamento já existente): guia inteira é
    # ignorada quando o prestador aparece nela. São as linhas em que Tipo/
    # Código estão vazios — inclusive linhas de planilhas antigas, que nunca
    # tiveram essas duas colunas.
    def _e_linha_de_protecao_total(linha):
        if not tem_colunas_fragmentacao:
            return True
        tipo = str(linha.get('Tipo', '')).strip().upper()
        return tipo not in ('PLANO', 'PROCEDIMENTO')

    set_blindagem = set(
        limpar_numero(r['Código Prestador Protegido'])
        for _, r in df_blindagem.iterrows()
        if pd.notna(r.get('Código Prestador Protegido')) and _e_linha_de_protecao_total(r)
    ) if not df_blindagem.empty and 'Código Prestador Protegido' in df_blindagem.columns else set()

    # 🆕 NOVA REGRA: contratos de fragmentação por prestador — linhas em que
    # Tipo = PLANO ou PROCEDIMENTO, indicando planos/procedimentos contratados
    # para aquele prestador (usado para decidir o que sai do arquivo principal
    # e vai para um fragmento de honorários daquele prestador). Guardado como
    # {codigo_prestador: {'planos': {...}, 'procedimentos': {...}}}.
    dict_fragmentacao = {}
    if tem_colunas_fragmentacao:
        for _, r in df_blindagem.iterrows():
            prestador_frag = limpar_numero(r.get('Código Prestador Protegido', ''))
            tipo = str(r.get('Tipo', '')).strip().upper()
            codigo_bruto = r.get('Código', '')
            if not prestador_frag or tipo not in ('PLANO', 'PROCEDIMENTO') or pd.isna(codigo_bruto) or limpar_numero(codigo_bruto) == '':
                continue
            cfg = dict_fragmentacao.setdefault(prestador_frag, {'planos': set(), 'procedimentos': set()})
            if tipo == 'PLANO':
                cfg['planos'].add(limpar_numero(codigo_bruto))
            else:
                cfg['procedimentos'].add(padronizar_codigo_8_digitos(codigo_bruto))
    fragmentos_coletados = {}  # {codigo_prestador: [itens fragmentados desta execução]}

    df_itens = dfs.get('itens', pd.DataFrame()) if isinstance(dfs, dict) else pd.DataFrame()
    dict_itens = {padronizar_codigo_8_digitos(k): padronizar_codigo_8_digitos(v) for k, v in zip(df_itens['Código Incorreto'], df_itens['Código Correto']) if pd.notna(k)} if not df_itens.empty and 'Código Incorreto' in df_itens.columns else {}

    df_unidades = dfs.get('unidades', pd.DataFrame()) if isinstance(dfs, dict) else pd.DataFrame()
    dict_unidades = {padronizar_codigo_8_digitos(r['Código do Item']): limpar_numero(r['Unidade de Medida Correta']) for _, r in df_unidades.iterrows() if pd.notna(r.get('Código do Item'))} if not df_unidades.empty and 'Código do Item' in df_unidades.columns else {}

    df_anvisa = dfs.get('anvisa', pd.DataFrame()) if isinstance(dfs, dict) else pd.DataFrame()
    dict_anvisa = {padronizar_codigo_8_digitos(r['Código do Item']): r for _, r in df_anvisa.iterrows() if pd.notna(r.get('Código do Item'))} if not df_anvisa.empty and 'Código do Item' in df_anvisa.columns else {}

    df_procedimentos = dfs.get('procedimentos', pd.DataFrame()) if isinstance(dfs, dict) else pd.DataFrame()
    dict_procedimentos = {padronizar_codigo_8_digitos(r['Código do Procedimento']): r for _, r in df_procedimentos.iterrows() if pd.notna(r.get('Código do Procedimento'))} if not df_procedimentos.empty and 'Código do Procedimento' in df_procedimentos.columns else {}

    guias_int = [(g, 'internacao') for g in root.findall('.//ans:guiaResumoInternacao', NS)]
    guias_sadt = [(g, 'sadt') for g in root.findall('.//ans:guiaSP-SADT', NS)]
    todas_guias = guias_int + guias_sadt

    for indice_guia, (guia, tipo_guia) in enumerate(todas_guias, start=1):
        try:
            prestador_elem = guia.find('.//ans:dadosPrestador/ans:codigoPrestadorNaOperadora', NS)
            if prestador_elem is None:
                prestador_elem = guia.find('.//ans:dadosContratado/ans:codigoPrestadorNaOperadora', NS)
            if prestador_elem is not None and limpar_numero(prestador_elem.text) in set_blindagem:
                auditoria['guias_blindadas'].append(f"Guia ignorada (Prestador {limpar_numero(prestador_elem.text)} protegido)")
                continue

            eh_unimed_0014 = False
            if tipo_guia == 'internacao':
                carteira_elem = guia.find('.//ans:dadosBeneficiario/ans:numeroCarteira', NS)
                numero_carteira = limpar_numero(carteira_elem.text) if carteira_elem is not None and carteira_elem.text else ""
                eh_unimed_0014 = identificar_plano_pela_carteira(numero_carteira) == '0014'

            # --- SUBSTITUIÇÃO DE EQUIPE EM GUIAS SADT ---
            if tipo_guia == 'sadt':
                for eq_sadt in guia.findall('.//ans:equipeSadt', NS):
                    nome_prof_elem = eq_sadt.find('ans:nomeProf', NS)
                    if nome_prof_elem is not None and nome_prof_elem.text:
                        nome_orig_xml = nome_prof_elem.text.strip().upper()
                        
                        if nome_orig_xml in dict_equipe_sadt:
                            regra = dict_equipe_sadt[nome_orig_xml]
                            
                            if regra['nome_novo']: nome_prof_elem.text = regra['nome_novo']
                            
                            if regra['crm_novo']:
                                crm_el = eq_sadt.find('ans:numeroConselhoProfissional', NS)
                                if crm_el is not None: crm_el.text = regra['crm_novo']
                                else:
                                    crm_el = ET.Element(ans_tag('numeroConselhoProfissional'))
                                    crm_el.text = regra['crm_novo']
                                    eq_sadt.append(crm_el)
                                    
                            if regra['cbo_novo']:
                                cbos_existentes = [c for c in eq_sadt.iter() if tag_limpa(c) in ['CBOS', 'codigoCBOS', 'codigoCBO']]
                                if cbos_existentes:
                                    cbos_existentes[0].text = regra['cbo_novo']
                                    for c_extra in cbos_existentes[1:]:
                                        for parent in eq_sadt.iter():
                                            if c_extra in list(parent): parent.remove(c_extra)
                                else:
                                    cbo_el = ET.Element(ans_tag('CBOS'))
                                    cbo_el.text = regra['cbo_novo']
                                    eq_sadt.append(cbo_el)
                                    
                            if regra['grau_novo']:
                                grau_el = eq_sadt.find('ans:grauPart', NS)
                                if grau_el is not None: grau_el.text = regra['grau_novo']
                                else:
                                    grau_el = ET.Element(ans_tag('grauPart'))
                                    grau_el.text = regra['grau_novo']
                                    eq_sadt.insert(0, grau_el)
                                    
                            if regra['conselho_novo']:
                                cons_el = eq_sadt.find('ans:conselho', NS)
                                if cons_el is not None: cons_el.text = regra['conselho_novo']
                                else:
                                    cons_el = ET.Element(ans_tag('conselho'))
                                    cons_el.text = regra['conselho_novo']
                                    eq_sadt.append(cons_el)
                                    
                            if regra['uf_nova']:
                                uf_el = eq_sadt.find('ans:UF', NS)
                                if uf_el is not None: uf_el.text = regra['uf_nova']
                                else:
                                    uf_el = ET.Element(ans_tag('UF'))
                                    uf_el.text = regra['uf_nova']
                                    eq_sadt.append(uf_el)
                                    
                            if regra['cod_op_novo']:
                                cod_prof_el = eq_sadt.find('ans:codProfissional', NS)
                                if cod_prof_el is None:
                                    cod_prof_el = ET.Element(ans_tag('codProfissional'))
                                    eq_sadt.append(cod_prof_el)
                                
                                op_el = cod_prof_el.find('ans:codigoPrestadorNaOperadora', NS)
                                if op_el is not None: op_el.text = regra['cod_op_novo']
                                else:
                                    op_el = ET.Element(ans_tag('codigoPrestadorNaOperadora'))
                                    op_el.text = regra['cod_op_novo']
                                    cod_prof_el.append(op_el)
                                    
                            auditoria['medicos_trocados'].append(f"Guia SADT (Equipe Completa): Mapeamento de '{nome_orig_xml}' substituído com sucesso.")

            # --- PROCEDIMENTOS E CBOS DE MÉDICOS ---
            procs_container = guia.find('.//ans:procedimentosExecutados', NS)
            if procs_container is not None:
                procs_para_remover = []
                
                for proc_exec in procs_container.findall('ans:procedimentoExecutado', NS):
                    cod_proc_elem = proc_exec.find('.//ans:codigoProcedimento', NS)
                    cod_p = padronizar_codigo_8_digitos(cod_proc_elem.text) if cod_proc_elem is not None and cod_proc_elem.text else ""
                    
                    is_protected = cod_p.startswith(('4', '2', '04', '02'))
                    equipes_iniciais = proc_exec.findall('ans:identEquipe', NS) + proc_exec.findall('ans:equipeSadt', NS)
                    equipes_remover = []
                    
                    for eq in equipes_iniciais:
                        nome_prof_elem = eq.find('.//ans:nomeProf', NS)
                        nome_prof = nome_prof_elem.text.strip().upper() if nome_prof_elem is not None and nome_prof_elem.text else ""
                        
                        if tipo_guia == 'internacao' and eh_unimed_0014 and nome_prof in set_conveniados:
                            if not is_protected:
                                equipes_remover.append(eq)
                                auditoria['conveniados_excluidos'].append(f"Removido médico(a) '{nome_prof}' do procedimento {cod_p} (Carteira: {numero_carteira})")
                    
                    for eq in equipes_remover:
                        proc_exec.remove(eq)
                    
                    equipes_restantes = proc_exec.findall('ans:identEquipe', NS) + proc_exec.findall('ans:equipeSadt', NS)
                    if len(equipes_iniciais) > 0 and len(equipes_restantes) == 0:
                        procs_para_remover.append(proc_exec)
                        continue 
                    
                    if cod_p in dict_procedimentos:
                        regra_p = dict_procedimentos[cod_p]
                        detalhes_proc = []
                        
                        grau_val_bruto = str(regra_p.get('Grau Part Obrigatório', '')).strip().upper()
                        if grau_val_bruto == 'EXCLUIR':
                            qtd_equipe_removida = len(equipes_restantes)
                            for eq in list(equipes_restantes):
                                proc_exec.remove(eq)
                            equipes_restantes = []
                            if qtd_equipe_removida:
                                detalhes_proc.append(f"Equipe do procedimento excluída ({qtd_equipe_removida} profissional(is) removido(s))")
                        else:
                            grau_val = limpar_numero(grau_val_bruto)
                            if grau_val:
                                for eq in equipes_restantes:
                                    target_node = eq if tag_limpa(eq) == 'equipeSadt' else (eq.find('ans:identificacaoEquipe', NS) or eq)
                                    grau_elem = target_node.find('ans:grauPart', NS)
                                    if grau_elem is not None: grau_elem.text = grau_val
                                    else:
                                        grau_elem = ET.Element(ans_tag('grauPart'))
                                        grau_elem.text = grau_val
                                        target_node.insert(0, grau_elem)
                                    
                                    for parent in eq.iter():
                                        for bad_grau in parent.findall('ans:grauParticipacao', NS): parent.remove(bad_grau)
                                            
                                detalhes_proc.append(f"Grau inserido: {grau_val}")
                            
                        quantidade_elem = proc_exec.find('ans:quantidadeExecutada', NS)
                        indent_tail = quantidade_elem.tail if quantidade_elem is not None else None

                        def _normaliza_via_tecnica(valor):
                            return str(int(valor)) if valor.isdigit() else valor

                        via_val = str(regra_p.get('Via de Acesso (1, 2 ou EXCLUIR)', '')).strip().upper()
                        via_elem = proc_exec.find('ans:viaAcesso', NS)
                        if via_val == 'EXCLUIR' and via_elem is not None:
                            proc_exec.remove(via_elem)
                            via_elem = None
                            detalhes_proc.append("Via de Acesso excluída")
                        elif via_val in ['1', '2', '01', '02']:
                            via_val = _normaliza_via_tecnica(via_val)
                            if via_elem is not None: via_elem.text = via_val
                            else:
                                via_elem = ET.Element(ans_tag('viaAcesso'))
                                via_elem.text = via_val
                                via_elem.tail = indent_tail
                                proc_exec.insert(indice_apos(proc_exec, quantidade_elem), via_elem)
                            detalhes_proc.append(f"Via de Acesso ajustada: {via_val}")
                            
                        tec_val = str(regra_p.get('Técnica (1, 2 ou EXCLUIR)', '')).strip().upper()
                        tec_elem = proc_exec.find('ans:tecnicaUtilizada', NS)
                        if tec_val == 'EXCLUIR' and tec_elem is not None:
                            proc_exec.remove(tec_elem)
                            detalhes_proc.append("Técnica excluída")
                        elif tec_val in ['1', '2', '01', '02']:
                            tec_val = _normaliza_via_tecnica(tec_val)
                            if tec_elem is not None: tec_elem.text = tec_val
                            else:
                                tec_elem = ET.Element(ans_tag('tecnicaUtilizada'))
                                tec_elem.text = tec_val
                                tec_elem.tail = indent_tail
                                ref_apos = via_elem if via_elem is not None else quantidade_elem
                                proc_exec.insert(indice_apos(proc_exec, ref_apos), tec_elem)
                            detalhes_proc.append(f"Técnica ajustada: {tec_val}")
                            
                        if detalhes_proc: auditoria['procedimentos_ajustados'].append(f"Proc {cod_p}: " + " | ".join(detalhes_proc))

                    # AJUSTES DE CBO E CÓDIGO OPERADORA DOS MÉDICOS
                    for eq in equipes_restantes:
                        nome_prof_elem = eq.find('.//ans:nomeProf', NS)
                        nome_prof = nome_prof_elem.text.strip().upper() if nome_prof_elem is not None and nome_prof_elem.text else ""
                        
                        if nome_prof in set_conveniados: continue 
                        
                        if nome_prof in dict_medicos:
                            regra_m = dict_medicos[nome_prof]
                            cbo_novo = limpar_numero(regra_m.get('CBO Correto', ''))
                            
                            target_node = eq if tag_limpa(eq) == 'equipeSadt' else (eq.find('ans:identificacaoEquipe', NS) or eq)

                            # Busca qualquer tag de CBO existente na estrutura
                            cbos_existentes = [elem for elem in eq.iter() if tag_limpa(elem) in ['CBOS', 'codigoCBOS', 'codigoCBO']]

                            if cbo_novo != '':
                                if cbos_existentes:
                                    # Atualiza o CBO original diretamente
                                    primeiro_cbo = cbos_existentes[0]
                                    if primeiro_cbo.text != cbo_novo:
                                        primeiro_cbo.text = cbo_novo
                                        auditoria['cbos'].append(f"Médico(a) '{nome_prof}': CBO alterado para {cbo_novo}")
                                    
                                    # Se houver duplicatas por erro antigo, remove as extras
                                    for c_extra in cbos_existentes[1:]:
                                        for parent in eq.iter():
                                            if c_extra in list(parent): parent.remove(c_extra)
                                else:
                                    # Insere o novo CBO dentro do nó correto (identificacaoEquipe / equipeSadt)
                                    novo_cbo = ET.Element(ans_tag('CBOS'))
                                    novo_cbo.text = cbo_novo
                                    target_node.append(novo_cbo)
                                    auditoria['cbos'].append(f"Médico(a) '{nome_prof}': CBO inserido ({cbo_novo})")
                            
                            substituir = str(regra_m.get('Substituir por Cód. Operadora', '')).strip().upper() == 'SIM'
                            cod_operadora = limpar_numero(regra_m.get('Código na Operadora', ''))
                            
                            if substituir and cod_operadora != '':
                                cod_prof_elem = eq.find('.//ans:codProfissional', NS)
                                if cod_prof_elem is not None:
                                    cpf_elem = cod_prof_elem.find('ans:cpfContratado', NS)
                                    cod_op_elem = cod_prof_elem.find('ans:codigoPrestadorNaOperadora', NS)
                                    if cpf_elem is not None:
                                        cpf_elem.tag = ans_tag('codigoPrestadorNaOperadora')
                                        cpf_elem.text = cod_operadora
                                        auditoria['cbos'].append(f"Médico(a) '{nome_prof}': CPF -> Cód. Operadora {cod_operadora}")
                                    elif cod_op_elem is not None:
                                        cod_op_elem.text = cod_operadora
                                        auditoria['cbos'].append(f"Médico(a) '{nome_prof}': Cód. Operadora alterado para {cod_operadora}")

                for p in procs_para_remover: procs_container.remove(p)

                # 🆕 NOVA REGRA: escalona horários de procedimentos duplicados (mesmo
                # código + data + horário) para evitar a crítica "Serviço duplicado".
                ajustar_horarios_duplicados(procs_container, auditoria)

                # 🆕 NOVA REGRA: fragmentação de procedimentos por prestador.
                # Regra lógica: fragmentar = prestador contratado (ex.: 220163)
                # AND plano do beneficiário contratado para esse prestador AND
                # procedimento contratado para esse prestador. Avaliada por
                # procedimento — nunca fragmenta a guia inteira por causa de
                # um único item elegível (ver PDF "regra_fragmentacao_prestador
                # _220163", seção 6 e casos 1 a 5).
                if tipo_guia == 'internacao' and dict_fragmentacao:
                    plano_beneficiario = identificar_plano_pela_carteira(numero_carteira)
                    for proc_exec in list(procs_container.findall('ans:procedimentoExecutado', NS)):
                        equipes_proc = proc_exec.findall('ans:identEquipe', NS) + proc_exec.findall('ans:equipeSadt', NS)
                        prestadores_do_proc = set()
                        for eq in equipes_proc:
                            cod_eq = eq.find('.//ans:codProfissional/ans:codigoPrestadorNaOperadora', NS)
                            if cod_eq is not None and cod_eq.text:
                                prestadores_do_proc.add(limpar_numero(cod_eq.text))

                        for prestador_frag, cfg_frag in dict_fragmentacao.items():
                            if prestador_frag not in prestadores_do_proc:
                                continue  # Condição 1 (prestador): não é deste prestador
                            if plano_beneficiario not in cfg_frag['planos']:
                                continue  # Condição 2 (plano): plano não contratado para este prestador
                            cod_proc_elem = proc_exec.find('.//ans:codigoProcedimento', NS)
                            cod_proc_frag = padronizar_codigo_8_digitos(cod_proc_elem.text) if cod_proc_elem is not None and cod_proc_elem.text else ""
                            if cod_proc_frag not in cfg_frag['procedimentos']:
                                continue  # Condição 3 (procedimento): procedimento não contratado para este prestador

                            # As 3 condições bateram simultaneamente: retira do
                            # arquivo principal e leva para o fragmento deste
                            # prestador (agrupado por guia de origem).
                            fragmentos_coletados.setdefault(prestador_frag, []).append({
                                'guia': guia, 'proc_exec': proc_exec, 'plano': plano_beneficiario, 'cod_proc': cod_proc_frag,
                            })
                            procs_container.remove(proc_exec)

                            valor_elem_frag = proc_exec.find('ans:valorTotal', NS)
                            try:
                                valor_removido = float(valor_elem_frag.text) if valor_elem_frag is not None and valor_elem_frag.text else 0.0
                            except ValueError:
                                valor_removido = 0.0
                            valor_total_guia = guia.find('.//ans:valorTotal', NS)
                            if valor_total_guia is not None and valor_removido:
                                for campo_valor in ('valorProcedimentos', 'valorTotalGeral'):
                                    campo_elem = valor_total_guia.find(f'ans:{campo_valor}', NS)
                                    if campo_elem is not None and campo_elem.text:
                                        try:
                                            campo_elem.text = f"{float(campo_elem.text) - valor_removido:.2f}"
                                        except ValueError:
                                            pass

                            auditoria['fragmentados'].append(
                                f"Procedimento {cod_proc_frag} (Plano {plano_beneficiario}) retirado do arquivo "
                                f"principal e movido para o fragmento de honorários do prestador {prestador_frag}."
                            )
                            break  # um procedimento só pode ir para o fragmento de um único prestador


            despesas_container = guia.find('.//ans:outrasDespesas', NS)
            if despesas_container is not None:
                for despesa in despesas_container.findall('ans:despesa', NS):
                    servicos = despesa.find('ans:servicosExecutados', NS)
                    if servicos is not None:
                        cod_item_elem = servicos.find('.//ans:codigoProcedimento', NS)
                        cod_item = padronizar_codigo_8_digitos(cod_item_elem.text) if cod_item_elem is not None and cod_item_elem.text else ""
                        cod_original_log = cod_item
                        
                        if cod_item in dict_itens:
                            cod_novo = dict_itens[cod_item]
                            cod_item_elem.text = cod_novo
                            cod_item = cod_novo
                            auditoria['itens'].append(f"Item alterado de {cod_original_log} para {cod_novo}")

                        if cod_item in ['60034335', '60034343']:
                            h_ini, h_fim, qtd_ex = servicos.find('ans:horaInicial', NS), servicos.find('ans:horaFinal', NS), servicos.find('ans:quantidadeExecutada', NS)
                            if h_ini is not None and h_fim is not None and qtd_ex is not None:
                                h_ini_novo, h_fim_novo, ok = calcular_tempo_oxigenio(h_ini.text, qtd_ex.text, cod_item)
                                if ok:
                                    if h_ini.text != h_ini_novo or h_fim.text != h_fim_novo:
                                        auditoria['oxigenio'].append(f"Oxigênio {cod_item}: Hora Inicial/Final ajustadas para {h_ini_novo} / {h_fim_novo}")
                                    h_ini.text = h_ini_novo
                                    h_fim.text = h_fim_novo
                                else:
                                    auditoria['erros'].append(f"Item {cod_item}: não foi possível recalcular hora de O² (horaInicial='{h_ini.text}', qtd='{qtd_ex.text}') — mantido valor original")

                        if cod_item in dict_unidades:
                            unidade_elem = servicos.find('ans:unidadeMedida', NS)
                            val_unidade = dict_unidades[cod_item].zfill(3) if dict_unidades[cod_item].isdigit() else dict_unidades[cod_item]
                            if unidade_elem is not None: unidade_elem.text = val_unidade
                            else:
                                unidade_elem = ET.Element(ans_tag('unidadeMedida'))
                                unidade_elem.text = val_unidade
                                servicos.append(unidade_elem)
                            auditoria['unidades'].append(f"Item {cod_item}: Unidade ajustada para {val_unidade}")

                        if cod_item in dict_anvisa:
                            regra_a = dict_anvisa[cod_item]
                            anvisa_alvo = limpar_numero(regra_a['Registro ANVISA'])
                            ref_alvo = limpar_numero(regra_a['Ref. Fabricante'])
                            add_anvisa = anvisa_alvo != "" and (servicos.find('ans:registroANVISA', NS) is None or not servicos.find('ans:registroANVISA', NS).text)
                            add_ref = ref_alvo != "" and (servicos.find('ans:codigoRefFabricante', NS) is None or not servicos.find('ans:codigoRefFabricante', NS).text)
                            if add_anvisa or add_ref:
                                reordenar_servico_executado(servicos, anvisa_alvo if add_anvisa else None, ref_alvo if add_ref else None)
                                detalhes_anv = []
                                if add_anvisa: detalhes_anv.append(f"ANVISA {anvisa_alvo}")
                                if add_ref: detalhes_anv.append(f"Ref {ref_alvo}")
                                auditoria['anvisa'].append(f"Item {cod_item}: Inserido " + " e ".join(detalhes_anv))

        except Exception as e:
            auditoria['erros'].append(f"Guia #{indice_guia} ({tipo_guia}): erro ao processar — {e}")

    # --- RECALCULO DE HASH (algoritmo OFICIAL da ANS: MD5 da concatenação do
    # conteúdo dos elementos-folha, na ordem do documento — não depende de
    # nenhum detalhe de formatação/serialização do XML) ---
    xml_bytes = recalcular_hash_e_serializar(tree, root)

    # 🆕 NOVA REGRA: gera um XML de honorários por prestador que recebeu ao
    # menos um procedimento fragmentado (nunca gera fragmento vazio).
    fragmentos = []
    for prestador_frag, itens_frag in fragmentos_coletados.items():
        if not itens_frag:
            continue
        tree_frag, root_frag = construir_fragmento_honorarios(root, prestador_frag, itens_frag)
        xml_frag_bytes = recalcular_hash_e_serializar(tree_frag, root_frag)
        fragmentos.append({'prestador': prestador_frag, 'xml_bytes': xml_frag_bytes, 'itens': itens_frag})

    return xml_bytes, auditoria, fragmentos

_PADRAO_TAG_LINHA = re.compile(r'<([\w:.-]+)>([^<]*)</\1>')

def calcular_diff_alteracoes(texto_base, texto_atual):
    """Gera uma lista aproximada de alterações (linha, campo, valor antigo,
    valor novo) comparando o texto linha a linha com difflib. Funciona bem
    para o padrão típico do TISS (uma tag por linha) — não é um diff XML
    semântico perfeito: se o usuário reformatar/reindentar um trecho inteiro,
    a mudança aparece de forma mais genérica (sem valor antigo/novo isolado)."""
    linhas_base = texto_base.splitlines()
    linhas_atual = texto_atual.splitlines()
    sm = difflib.SequenceMatcher(None, linhas_base, linhas_atual)
    alteracoes = []

    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            continue
        antigas = linhas_base[i1:i2]
        novas = linhas_atual[j1:j2]
        pares = list(zip(antigas, novas)) if len(antigas) == len(novas) else []

        if pares:
            for offset, (linha_antiga, linha_nova) in enumerate(pares):
                if linha_antiga == linha_nova:
                    continue
                m_antiga = _PADRAO_TAG_LINHA.search(linha_antiga)
                m_nova = _PADRAO_TAG_LINHA.search(linha_nova)
                numero_linha = j1 + offset + 1
                if m_antiga and m_nova and m_antiga.group(1) == m_nova.group(1):
                    alteracoes.append({
                        'linha': numero_linha,
                        'campo': m_antiga.group(1),
                        'antes': m_antiga.group(2),
                        'depois': m_nova.group(2),
                    })
                else:
                    alteracoes.append({
                        'linha': numero_linha,
                        'campo': None,
                        'antes': linha_antiga.strip(),
                        'depois': linha_nova.strip(),
                    })
        else:
            # Bloco de tamanho diferente (linhas inseridas/removidas) — não dá
            # pra parear 1-a-1, mostra como um bloco genérico de alteração.
            numero_linha = j1 + 1 if novas else i1 + 1
            alteracoes.append({
                'linha': numero_linha,
                'campo': None,
                'antes': ' / '.join(l.strip() for l in antigas) if antigas else '(nada)',
                'depois': ' / '.join(l.strip() for l in novas) if novas else '(removido)',
            })

    return alteracoes

TITULOS_AMIGAVEIS_AUDITORIA = {
    'medicos_trocados': '🔀 Médicos e CRMs Substituídos',
    'cbos': '👩‍⚕️ Médicos e CBOs Alterados',
    'itens': '🔄 Itens e Medicamentos Traduzidos',
    'anvisa': '🩺 Registros ANVISA Inseridos',
    'unidades': '📦 Unidades de Medida Ajustadas',
    'oxigenio': '⏱️ Tempos de Oxigênio Recalculados',
    'conveniados_excluidos': '🤝 Médicos Conveniados Removidos',
    'procedimentos_ajustados': '⚙️ Procedimentos Ajustados (Grau/Via/Técnica)',
    'guias_blindadas': '🛡️ Guia(s) Blindada(s)',
    'erros': '⚠️ Avisos e Erros Durante o Processamento',
    'valores_negativos': '➖ Valores Negativos Corrigidos',
    'motivo_encerramento': '🚪 Motivo de Encerramento (11 ➔ 12)',
    'horarios_duplicados': '⏰ Horários Escalonados (Anti-Duplicidade)',
    'fragmentados': '📦 Procedimentos Fragmentados para Outro Prestador'
}


# ==========================================
# TEMA VISUAL — identidade própria do Validador TISS: acentos em teal
# (mais sóbrio que o azul padrão do Quasar, combina com o tom "saúde/
# faturamento"), sombras suaves e cantos arredondados no lugar do visual
# "flat" anterior, com transições sutis nos estados de hover.
# ==========================================
ui.add_head_html("""
<style>
    :root {
        --tiss-accent: #0f766e;
        --tiss-accent-suave: #ccfbf1;
        --tiss-borda: #e2e8f0;
        --tiss-bg: #f4f7f6;
        --tiss-bg-painel: #ffffff;
        --tiss-texto: #374151;
        --tiss-texto-forte: #1f2937;
        --tiss-texto-suave: #4b5563;
        --tiss-sombra: rgba(15, 23, 42, 0.06);
        --tiss-sombra-hover: rgba(15, 23, 42, 0.08);
        --tiss-diff-bg: #fffbeb;
        --tiss-diff-borda: #d97706;
        --tiss-diff-linha: #92400e;
    }
    /* Tema escuro: aplicado quando o Quasar liga o dark mode (ver botão de
       tema no topo da página, controlado por ui.dark_mode() no Python). */
    body.body--dark {
        --tiss-accent: #2dd4bf;
        --tiss-accent-suave: #134e4a;
        --tiss-borda: #334155;
        --tiss-bg: #0f172a;
        --tiss-bg-painel: #1e293b;
        --tiss-texto: #cbd5e1;
        --tiss-texto-forte: #f1f5f9;
        --tiss-texto-suave: #94a3b8;
        --tiss-sombra: rgba(0, 0, 0, 0.35);
        --tiss-sombra-hover: rgba(0, 0, 0, 0.5);
        --tiss-diff-bg: #3a2f0f;
        --tiss-diff-borda: #d97706;
        --tiss-diff-linha: #fbbf24;
    }

    body { background-color: var(--tiss-bg) !important; transition: background-color .15s ease; }

    .q-card {
        border-radius: 10px !important;
        background-color: var(--tiss-bg-painel) !important;
        color: var(--tiss-texto-forte) !important;
        transition: background-color .15s ease, color .15s ease;
    }

    .tiss-header, .tiss-toolbar, .tiss-statusbar, .tiss-panel {
        background-color: var(--tiss-bg-painel);
        border: 1px solid var(--tiss-borda);
        border-radius: 8px;
        box-shadow: 0 1px 3px var(--tiss-sombra);
        transition: box-shadow .15s ease, background-color .15s ease, border-color .15s ease;
    }
    .tiss-header {
        padding: 8px 14px;
        border-left: 4px solid var(--tiss-accent);
    }
    .tiss-toolbar { padding: 4px 8px; }
    .tiss-toolbar .q-btn {
        border-radius: 6px;
        transition: background-color .12s ease;
    }
    .tiss-toolbar .q-btn:hover {
        background-color: var(--tiss-accent-suave);
    }
    .tiss-statusbar { padding: 6px 14px; font-size: 12.5px; color: var(--tiss-texto); }
    .tiss-panel { padding: 10px; height: 74vh; overflow-y: auto; }
    .tiss-panel:hover { box-shadow: 0 2px 6px var(--tiss-sombra-hover); }

    .tiss-app-name { font-weight: 700; color: var(--tiss-accent); font-size: 15px; }
    .tiss-file-name { font-weight: 600; color: var(--tiss-texto); margin-left: 10px; transition: color .15s ease; }
    .tiss-file-name.modificado { color: #b45309; }

    .diff-item {
        border-left: 3px solid var(--tiss-diff-borda);
        background-color: var(--tiss-diff-bg);
        padding: 7px 9px;
        margin-bottom: 6px;
        border-radius: 5px;
        font-size: 12.5px;
        transition: box-shadow .12s ease, background-color .15s ease;
    }
    .diff-item:hover { box-shadow: 0 1px 4px var(--tiss-sombra-hover); }
    .diff-linha { color: var(--tiss-diff-linha); font-weight: 700; font-size: 11px; }
    .diff-campo { color: var(--tiss-texto-forte); font-weight: 600; }
    .diff-valores { color: var(--tiss-texto-suave); font-family: 'Consolas', monospace; font-size: 11.5px; }

    /* Ajusta, no tema escuro, as classes de texto tipo Tailwind usadas em
       vários pontos do app (avisos, status, rótulos secundários) para
       manter contraste legível sobre fundo escuro. */
    body.body--dark .text-gray-600, body.body--dark .text-gray-500 { color: #94a3b8 !important; }
    body.body--dark .text-red-700 { color: #f87171 !important; }
    body.body--dark .text-green-700 { color: #4ade80 !important; }
    body.body--dark .text-amber-700 { color: #fbbf24 !important; }
</style>
<script>
    // Aviso nativo do navegador ao tentar fechar/recarregar a aba com
    // alterações não salvas no editor de XML. O Python atualiza
    // window.__validadorTissAlterado a cada mudança de estado do editor
    // (veja atualizar_interface() em construir_editor_xml); aqui só ligamos
    // o listener uma única vez, no carregamento da página.
    window.__validadorTissAlterado = false;
    window.addEventListener('beforeunload', function (e) {
        if (window.__validadorTissAlterado) {
            e.preventDefault();
            e.returnValue = '';
            return '';
        }
    });
</script>
""", shared=True)


@ui.page('/')
def pagina_principal():
    ui.colors(primary='#0f766e')  # identidade visual do app: teal em vez do azul padrão do Quasar

    # ======================================================================
    # ESTADO DESTA SESSÃO/ABA DO NAVEGADOR — cada usuário que abrir a
    # aplicação recebe seu próprio dicionário 'estado', isolado dos demais
    # (importante: os arquivos e edições de uma pessoa NUNCA aparecem para
    # outra, já que isso vai ser publicado para múltiplos usuários).
    #
    # As regras de negócio (médicos, procedimentos, itens etc.) são só LIDAS
    # do Google Sheets aqui — a edição delas foi retirada do app de propósito:
    # como o app é usado por várias pessoas, mas só algumas devem poder
    # alterar as regras, a edição fica restrita a quem tem acesso direto à
    # planilha, evitando que alguém sem contexto mude uma regra sem querer.
    # ======================================================================
    dfs_iniciais, avisos_sheets = carregar_tabelas_do_sheets()
    estado = {
        'dfs': dfs_iniciais,
        'arquivos_pendentes': [],   # [(nome, bytes), ...] aguardando processamento
        'resultados_lote': [],
        'lote_id': 0,
        'arquivo_selecionado': None,  # nome do arquivo escolhido no seletor, para sobreviver a um refresh do painel
        'tema_escuro': app.storage.user.get('tiss_tema_escuro', False),  # preferência de tema, lembrada por navegador
    }
    editores = {}  # chave: (lote_id, nome_arquivo) -> dict com o estado do editor daquele arquivo

    # ==========================================
    # TEMA CLARO / ESCURO — controla o dark mode nativo do Quasar (que
    # dispara as regras "body.body--dark" do CSS acima) e troca o tema do
    # editor CodeMirror de cada aba de XML já aberta. A escolha é lembrada
    # por navegador (app.storage.user), então persiste entre visitas.
    # ==========================================
    modo_escuro = ui.dark_mode(value=estado['tema_escuro'])

    def alternar_tema(e):
        estado['tema_escuro'] = e.value
        app.storage.user['tiss_tema_escuro'] = e.value
        modo_escuro.set_value(e.value)
        novo_tema_editor = 'basicDark' if e.value else 'basicLight'
        for ed in editores.values():
            if ed.get('ui_editor') is not None:
                ed['ui_editor'].set_theme(novo_tema_editor)

    with ui.row().classes('w-full items-center justify-end gap-2'):
        ui.icon('light_mode').classes('text-sm')
        ui.switch(value=estado['tema_escuro'], on_change=alternar_tema).props('color=primary dense').tooltip('Alternar entre tema claro e escuro')
        ui.icon('dark_mode').classes('text-sm')

    with ui.column().classes('w-full max-w-none gap-2'):
        if avisos_sheets:
            with ui.expansion('⚠️ Avisos ao carregar as regras do Google Sheets', icon='warning').classes('w-full mb-2'):
                for a in avisos_sheets:
                    ui.label(f"• {a}").classes('text-sm text-amber-700')
        construir_aba_processamento(estado, editores)


# ==========================================================================
# ABA "PROCESSAR XMLs"
# ==========================================================================
def construir_aba_processamento(estado, editores):

    async def ao_receber_upload(e):
        conteudo = await e.file.read()
        estado['arquivos_pendentes'].append((e.file.name, conteudo))
        label_pendentes.text = f"📁 {len(estado['arquivos_pendentes'])} arquivo(s) selecionado(s)."

    with ui.card().classes('w-full'):
        ui.label('📜 Processamento de XMLs em Lote').classes('text-lg font-bold')
        ui.label('Arraste um ou vários arquivos XML gerados pelo seu sistema.').classes('text-sm text-gray-600')
        ui.upload(on_upload=ao_receber_upload, multiple=True, auto_upload=True).props('accept=.xml').classes('w-full')
        label_pendentes = ui.label('Nenhum arquivo selecionado ainda.').classes('text-sm text-gray-600')

        async def iniciar_correcao():
            if not estado['arquivos_pendentes']:
                ui.notify('Selecione ao menos um arquivo XML antes de continuar.', type='warning')
                return
            barra.visible = True
            resultados = []
            pendentes = estado['arquivos_pendentes']
            for i, (nome, conteudo) in enumerate(pendentes):
                resultado = {'nome': nome, 'xml_bytes': None, 'auditoria': None, 'falha_total': None}
                try:
                    xml_resultado, auditoria, fragmentos = processar_xml_tiss(io.BytesIO(conteudo), estado['dfs'])
                    resultado['xml_bytes'] = xml_resultado
                    resultado['auditoria'] = auditoria
                    resultados.append(resultado)
                    # 🆕 Cada fragmento de honorários gerado (ex.: prestador
                    # 220163) vira um resultado independente, com nome próprio
                    # — assim ele aparece no seletor de arquivos, pode ser
                    # editado/validado como qualquer outro, e entra junto no
                    # ZIP de "Baixar Todos", reaproveitando toda a infra já
                    # existente em vez de criar um caminho especial para ele.
                    for frag in fragmentos:
                        nome_frag = f"HONORARIOS_{frag['prestador']}_{nome}"
                        auditoria_frag = {chave: [] for chave in auditoria}
                        auditoria_frag['fragmentados'] = [
                            f"Procedimento {item['cod_proc']} (Plano {item['plano']}) — origem: '{nome}'."
                            for item in frag['itens']
                        ]
                        resultados.append({
                            'nome': nome_frag, 'xml_bytes': frag['xml_bytes'],
                            'auditoria': auditoria_frag, 'falha_total': None,
                        })
                except Exception as e:
                    resultado['falha_total'] = str(e)
                    resultados.append(resultado)
                barra.set_value((i + 1) / len(pendentes))
            # Junta os arquivos deste lote aos que já estavam na lista, em vez
            # de substituir tudo. Se um arquivo com o mesmo nome já tiver sido
            # processado antes, a versão mais nova (deste clique) substitui a
            # antiga; arquivos com nomes diferentes de lotes anteriores
            # continuam disponíveis para seleção.
            existentes_por_nome = {r['nome']: r for r in estado['resultados_lote']}
            for r in resultados:
                existentes_por_nome[r['nome']] = r
            estado['resultados_lote'] = list(existentes_por_nome.values())
            estado['lote_id'] += 1
            estado['arquivos_pendentes'] = []
            label_pendentes.text = 'Nenhum arquivo selecionado ainda.'
            barra.visible = False
            painel_resultados.refresh()

        def limpar_lista_processados():
            def confirmar_limpeza():
                estado['resultados_lote'] = []
                estado['arquivo_selecionado'] = None
                estado['lote_id'] += 1
                painel_resultados.refresh()
                ui.notify('Lista de arquivos processados limpa.', type='info')
                dialogo_limpar.close()

            tem_edicao_pendente = any(
                ed['texto_atual'] != ed['texto_base'] for ed in editores.values()
            )
            if not tem_edicao_pendente:
                confirmar_limpeza()
                return

            with ui.dialog() as dialogo_limpar, ui.card():
                ui.label('Limpar lista com alterações não salvas?').classes('text-base font-bold')
                ui.label('Pelo menos um dos arquivos processados tem edições que ainda não foram '
                          'salvas. Limpar a lista agora descarta essas edições.') \
                    .classes('text-sm text-gray-600')
                with ui.row().classes('w-full justify-end gap-2 mt-2'):
                    ui.button('Cancelar', on_click=dialogo_limpar.close).props('flat')
                    ui.button('Limpar mesmo assim', color='negative', on_click=confirmar_limpeza)
            dialogo_limpar.open()

        with ui.row().classes('w-full mt-2 gap-2 no-wrap'):
            ui.button('🚀 Iniciar Correção Automática', on_click=iniciar_correcao, color='primary').classes('flex-grow')
            ui.button('🧹 Limpar Lista', on_click=limpar_lista_processados).props('flat')
        barra = ui.linear_progress(value=0).classes('w-full mt-1')
        barra.visible = False

    painel_resultados(estado, editores)


@ui.refreshable
def painel_resultados(estado, editores):
    resultados = estado['resultados_lote']
    if not resultados:
        return

    with ui.card().classes('w-full mt-2'):
        ui.label('📊 Resultado da Auditoria').classes('text-lg font-bold')

        sucesso = [r for r in resultados if not r.get('falha_total')]
        falhas = [r for r in resultados if r.get('falha_total')]

        if falhas:
            with ui.expansion(f'❌ {len(falhas)} arquivo(s) com falha total', icon='error', value=True).classes('w-full'):
                for r in falhas:
                    ui.label(f"{r['nome']}: {r['falha_total']}").classes('text-sm text-red-700')

        if not sucesso:
            return

        nomes = [r['nome'] for r in sucesso]
        valor_inicial = estado['arquivo_selecionado'] if estado['arquivo_selecionado'] in nomes else nomes[0]
        if len(sucesso) > 1:
            def baixar_zip():
                buffer = io.BytesIO()
                with zipfile.ZipFile(buffer, 'w', zipfile.ZIP_DEFLATED) as zf:
                    for r in sucesso:
                        zf.writestr(f"PRONTO_{r['nome']}", r['xml_bytes'])
                ui.download.content(buffer.getvalue(), 'XMLS_CORRIGIDOS.zip', media_type='application/zip')
            ui.button('📦 Baixar Todos os XMLs Corrigidos (.ZIP)', on_click=baixar_zip, color='primary').classes('w-full')
            seletor_arquivo = ui.select(nomes, value=valor_inicial, label='Arquivo selecionado').classes('w-full mt-2')
        else:
            seletor_arquivo = None

        nome_escolhido = seletor_arquivo.value if seletor_arquivo else nomes[0]
        estado['arquivo_selecionado'] = nome_escolhido
        resultado = next(r for r in sucesso if r['nome'] == nome_escolhido)

        aud = resultado.get('auditoria') or {}
        with ui.row().classes('w-full mt-2 gap-6'):
            ui.label(f"🔀 Médicos Trocados: {len(aud.get('medicos_trocados', []))}").classes('text-sm')
            ui.label(f"👩‍⚕️ CBOs/Cods: {len(aud.get('cbos', []))}").classes('text-sm')
            ui.label(f"➖ Valores Negativos: {len(aud.get('valores_negativos', []))}").classes('text-sm')
            ui.label(f"🔄 Itens Traduzidos: {len(aud.get('itens', []))}").classes('text-sm')
            ui.label(f"⏱️ Tempos O²: {len(aud.get('oxigenio', []))}").classes('text-sm')
            ui.label(f"🛡️ Guia(s) Blindada(s): {len(aud.get('guias_blindadas', []))}").classes('text-sm')
        if aud.get('erros'):
            ui.label(f"⚠️ {len(aud['erros'])} aviso(s)/erro(s) pontual(is) durante o processamento.").classes('text-sm text-amber-700 mt-1')

        def ao_trocar_arquivo(e):
            estado['arquivo_selecionado'] = e.value
            painel_resultados.refresh()

        if seletor_arquivo:
            seletor_arquivo.on_value_change(ao_trocar_arquivo)

    construir_editor_xml(estado, editores, resultado)


# ==========================================================================
# EDITOR DE XML ESTILO DESKTOP (header + toolbar + editor/painel + status bar)
# — usa as MESMAS funções de negócio já validadas na versão Streamlit.
# ==========================================================================
def construir_editor_xml(estado, editores, resultado):
    nome_arquivo = resultado['nome']
    lote_id = estado['lote_id']
    chave = (lote_id, nome_arquivo)

    if chave not in editores:
        # Carregamos o texto no editor sempre com quebras de linha \n (padrão
        # que o CodeMirror usa internamente). O arquivo processado vem com
        # \r\n (CRLF), e se deixássemos esse \r a mais em cada linha, ele cria
        # um descompasso entre "quantos caracteres o Python conta até um
        # ponto do texto" e "quantos caracteres o CodeMirror conta até esse
        # mesmo ponto" — um desvio que cresce a cada quebra de linha anterior
        # e pode fazer uma edição feita numa posição do texto ser aplicada
        # ligeiramente deslocada. O \r\n é reaplicado de qualquer forma na
        # hora de gerar o arquivo final (recalcular_hash_e_serializar), então
        # removê-lo aqui não afeta o arquivo salvo, só a edição em tela.
        xml_texto = resultado['xml_bytes'].decode('ISO-8859-1').replace('\r\n', '\n')
        editores[chave] = {
            'texto_original': xml_texto,
            'texto_base': xml_texto,
            'texto_atual': xml_texto,
            'salvo_alguma_vez': False,
            'hash_original': _extrair_hash_do_texto(xml_texto),
            'hash_atual': _extrair_hash_do_texto(xml_texto),
            'historico': [],
            'futuro': [],
            'erro_validacao': None,
            'ui_editor': None,  # referência ao CodeMirror desta aba, preenchida abaixo (usada para trocar o tema claro/escuro depois de aberto)
        }
    ed = editores[chave]

    # Sinaliza que a próxima mudança de valor do editor (CodeMirror) foi
    # feita pelo próprio código (desfazer, refazer, salvar, recarregar,
    # substituir), e não por digitação do usuário. Isso é necessário porque
    # editor.set_value(...) dispara o mesmo evento on_value_change que uma
    # tecla digitada dispararia — sem esse sinalizador, um "Desfazer" faria
    # a lógica de checkpoint de undo (em ao_digitar) tratar o próprio
    # desfazer como se fosse uma edição nova, empilhando de volta o estado
    # que acabou de ser removido do histórico.
    _evento_editor = {'ignorar_proximo': False}

    def _repor_valor_editor(texto):
        """Substitui todo o conteúdo do editor programaticamente. Limpamos
        primeiro e só depois preenchemos com o texto final: o CodeMirror do
        NiceGUI, ao receber um novo valor vindo do servidor, tenta aplicar
        apenas a "região modificada" (para preservar a posição do cursor)
        em vez de substituir o documento inteiro. Em edições grandes ou que
        tocam várias partes do texto (como desfazer/refazer ou "Substituir
        todos"), esse cálculo de patch parcial pode ocasionalmente
        dessincronizar o texto realmente armazenado no editor do texto
        exibido na tela. Forçar uma limpeza antes evita esse cálculo de
        patch (é sempre tratado como "inserir tudo do zero"), eliminando o
        risco de dessincronia.
        """
        _evento_editor['ignorar_proximo'] = True
        editor.set_value('')
        _evento_editor['ignorar_proximo'] = True
        editor.set_value(texto)
        # Qualquer reposição programática do conteúdo fecha a rajada de
        # digitação em andamento (se houver), para que a próxima tecla
        # digitada comece um novo checkpoint de desfazer a partir daqui —
        # sem isso, um "Salvar" ou "Substituir todos" feito no meio de uma
        # pausa de digitação poderia ficar "escondido" entre dois pontos do
        # histórico de desfazer.
        _debounce['em_rajada'] = False

    def definir_conteudo(novo_texto, empilhar_undo=True):
        if empilhar_undo:
            ed['historico'].append(ed['texto_atual'])
            ed['historico'][:] = ed['historico'][-50:]
            ed['futuro'].clear()
        ed['texto_atual'] = novo_texto
        _repor_valor_editor(novo_texto)
        atualizar_interface()

    with ui.column().classes('w-full gap-2 mt-2'):
        with ui.row().classes('w-full items-center justify-between tiss-header'):
            with ui.row().classes('items-center gap-0'):
                ui.label('📄 Validador TISS').classes('tiss-app-name')
                label_arquivo = ui.label(nome_arquivo).classes('tiss-file-name')
            botao_salvar_header = ui.button('Salvar', icon='save', color='primary')

        with ui.row().classes('w-full items-center tiss-toolbar gap-1'):
            botao_desfazer = ui.button(icon='undo').props('flat dense').tooltip('Desfazer')
            botao_refazer = ui.button(icon='redo').props('flat dense').tooltip('Refazer')
            with ui.button(icon='search').props('flat dense').tooltip('Localizar e substituir'):
                with ui.menu() as menu_localizar:
                    with ui.column().classes('p-3 gap-2').style('width: 320px'):
                        ui.label('Localizar e Substituir').classes('font-bold')
                        campo_localizar = ui.input('Localizar').classes('w-full')
                        campo_substituir = ui.input('Substituir por').classes('w-full')
                        resultado_busca = ui.label('').classes('text-xs text-gray-500')
                        with ui.row().classes('gap-1 w-full'):
                            botao_loc = ui.button('Localizar').props('flat dense size=sm')
                            botao_sub_um = ui.button('Substituir').props('flat dense size=sm')
                            botao_sub_todos = ui.button('Substituir todos', color='primary').props('dense size=sm')
            botao_validar = ui.button(icon='check_circle').props('flat dense').tooltip('Validar XML')
            botao_recarregar = ui.button(icon='refresh').props('flat dense').tooltip('Recarregar (descarta alterações)')
            botao_baixar = ui.button(icon='download').props('flat dense').tooltip('Baixar XML')
            botao_copiar = ui.button(icon='content_copy').props('flat dense').tooltip('Copiar código-fonte')

        with ui.row().classes('w-full gap-2 no-wrap').style('height: 76vh'):
            with ui.column().classes('gap-0').style('flex: 4; height: 100%'):
                tema_editor = 'basicDark' if estado.get('tema_escuro') else 'basicLight'
                editor = ui.codemirror(value=ed['texto_atual'], language='XML', theme=tema_editor) \
                    .classes('w-full h-full border').style('font-size: 13px')
                ed['ui_editor'] = editor
            with ui.column().classes('gap-0 tiss-panel').style('flex: 1; min-width: 260px'):
                ui.label('ALTERAÇÕES').classes('font-bold text-sm mb-1')
                painel_alteracoes = ui.column().classes('w-full gap-0')

        with ui.row().classes('w-full items-center tiss-statusbar gap-6'):
            status_arquivo = ui.label()
            status_validade = ui.label()
            status_linhas = ui.label()
            status_alteracoes = ui.label()
            status_hash = ui.html()

        with ui.expansion('📝 Ver Detalhes das Modificações Automáticas').classes('w-full'):
            aud = resultado.get('auditoria') or {}
            tem_alteracao = False
            for chave_aud, lista_logs in aud.items():
                if lista_logs:
                    tem_alteracao = True
                    ui.label(TITULOS_AMIGAVEIS_AUDITORIA.get(chave_aud, chave_aud)).classes('font-bold text-sm mt-1')
                    for item in lista_logs:
                        ui.label(f"• {item}").classes('text-xs text-gray-600')
            if not tem_alteracao:
                ui.label('Nenhuma alteração foi necessária neste XML.').classes('text-sm text-gray-500')

    # ---------------- Atualização da interface ----------------
    def atualizar_painel_diff(alterado):
        """Recalcula e redesenha o painel 'ALTERAÇÕES'. Isolado à parte porque
        é a operação mais cara aqui (roda um diff linha a linha no arquivo
        inteiro) — em XMLs grandes (1000+ linhas), rodar isso a cada tecla
        digitada pode deixar a digitação com uma leve travada. Por isso, ao
        digitar, essa função é chamada com atraso (debounce) em vez de a
        cada tecla; nas outras ações (desfazer, salvar, recarregar,
        substituir) ela roda imediatamente, já que são ações pontuais, não
        contínuas."""
        painel_alteracoes.clear()
        alteracoes = calcular_diff_alteracoes(ed['texto_base'], ed['texto_atual']) if alterado else []
        with painel_alteracoes:
            if alteracoes:
                ui.label(f"🟡 {len(alteracoes)} alteração(ões)").classes('text-sm mb-2')
                for alt in alteracoes[:60]:
                    campo = alt['campo'] or '(trecho alterado)'
                    ui.html(f"""
                        <div class="diff-item">
                            <div class="diff-linha">Linha {alt['linha']}</div>
                            <div class="diff-campo">{html.escape(campo)}</div>
                            <div class="diff-valores">{html.escape(alt['antes'])} → {html.escape(alt['depois'])}</div>
                        </div>
                    """)
            else:
                ui.label('Nenhuma alteração realizada.').classes('text-sm text-gray-500')
        status_alteracoes.text = (f"⚠ {len(alteracoes)} alteração(ões) não salva(s)" if alterado
                                   else ("💾 Alterações salvas" if ed['salvo_alguma_vez'] else "Sem alterações"))
        status_alteracoes.classes(replace='text-amber-700 font-semibold' if alterado else 'text-gray-600')

    def atualizar_interface(recalcular_diff=True):
        alterado = ed['texto_atual'] != ed['texto_base']
        label_arquivo.text = f"{nome_arquivo} *" if alterado else nome_arquivo
        label_arquivo.classes(replace='tiss-file-name modificado' if alterado else 'tiss-file-name')

        botao_salvar_header.set_enabled(alterado)
        botao_desfazer.set_enabled(bool(ed['historico']))
        botao_refazer.set_enabled(bool(ed['futuro']))

        try:
            ET.fromstring(ed['texto_atual'].encode('ISO-8859-1'))
            status_validade.text = '✓ XML válido'
            status_validade.classes(replace='text-green-700 font-semibold')
        except Exception:
            status_validade.text = '✕ XML inválido'
            status_validade.classes(replace='text-red-700 font-semibold')

        status_arquivo.text = html.escape(nome_arquivo)
        status_linhas.text = f"{len(ed['texto_atual'].splitlines())} linhas"

        hash_dif = ed['hash_atual'] != ed['hash_original']
        cor = 'color:#b45309;font-weight:600' if hash_dif else 'color:#374151'
        status_hash.content = (f"Hash original: <code>{ed['hash_original'] or '—'}</code> &nbsp;|&nbsp; "
                                f"<span style='{cor}'>Hash atual: <code>{ed['hash_atual'] or '—'}</code></span>")

        # Liga/desliga o aviso nativo do navegador de "sair sem salvar"
        # (registrado uma vez no <head> da página; aqui só atualizamos a flag).
        ui.run_javascript(f"window.__validadorTissAlterado = {str(alterado).lower()};")

        if recalcular_diff:
            atualizar_painel_diff(alterado)

    # ---------------- Eventos ----------------
    _debounce = {'timer': None, 'em_rajada': False}

    def _fim_da_rajada(alterado):
        # Marca o fim da pausa de digitação: a próxima tecla começa uma nova
        # rajada (e portanto um novo checkpoint de desfazer).
        _debounce['em_rajada'] = False
        atualizar_painel_diff(alterado)

    def ao_digitar(e):
        # Mudança de valor disparada pelo próprio código (desfazer, refazer,
        # salvar, recarregar, substituir) — não é digitação do usuário e não
        # deve mexer no histórico de desfazer nem reagendar o diff.
        if _evento_editor['ignorar_proximo']:
            _evento_editor['ignorar_proximo'] = False
            return

        if not _debounce['em_rajada']:
            # Início de uma nova rajada de digitação: guarda o texto de
            # ANTES dela como ponto de desfazer. Sem isso, digitar
            # diretamente no editor nunca alimentava o histórico — só ações
            # como "Substituir" ou "Recarregar" passavam por
            # definir_conteudo(), então os botões Desfazer/Refazer ficavam
            # sempre desabilitados (ou sem efeito) depois de uma edição
            # comum de texto.
            ed['historico'].append(ed['texto_atual'])
            ed['historico'][:] = ed['historico'][-50:]
            ed['futuro'].clear()
            _debounce['em_rajada'] = True

        ed['texto_atual'] = e.value
        # Atualização leve (label, botões, validade, status) a cada tecla —
        # é barata. O recálculo do diff (caro) é adiado: se o usuário digitar
        # de novo antes de 0.5s passar, o cálculo pendente é cancelado e
        # reagendado, então só roda de fato quando a digitação faz uma pausa.
        # É também essa mesma pausa que fecha a rajada atual do undo.
        alterado = ed['texto_atual'] != ed['texto_base']
        atualizar_interface(recalcular_diff=False)
        if _debounce['timer']:
            _debounce['timer'].deactivate()
        _debounce['timer'] = ui.timer(0.5, lambda: _fim_da_rajada(alterado), once=True)
    editor.on_value_change(ao_digitar)

    def salvar(_=None):
        novos_bytes, erro = validar_e_recalcular_xml_editado(ed['texto_atual'])
        if erro:
            ed['erro_validacao'] = erro
            ui.notify(f'❌ {erro}', type='negative', multi_line=True, close_button=True)
            return
        novo_texto_final = novos_bytes.decode('ISO-8859-1')
        definir_conteudo(novo_texto_final, empilhar_undo=False)
        ed['texto_base'] = novo_texto_final
        ed['hash_atual'] = _extrair_hash_do_texto(novo_texto_final)
        ed['salvo_alguma_vez'] = True
        resultado['xml_bytes'] = novos_bytes
        # Além de validar e recalcular o hash, já dispara o download do
        # arquivo final automaticamente. O "Salvar" nunca escreve nada no
        # disco por conta própria (o Python roda no servidor, não na máquina
        # de quem está usando o app) — quem efetivamente coloca o arquivo no
        # computador é sempre o download do navegador. Antes, isso exigia
        # dois cliques (Salvar, depois Baixar); agora sai em um só.
        ui.download.content(novos_bytes, f"PRONTO_{nome_arquivo}", media_type='application/xml')
        ui.notify('✅ Alterações salvas, hash recalculado e download iniciado.', type='positive')
    botao_salvar_header.on('click', salvar)

    def desfazer(_=None):
        if ed['historico']:
            ed['futuro'].append(ed['texto_atual'])
            anterior = ed['historico'].pop()
            ed['texto_atual'] = anterior
            _repor_valor_editor(anterior)
            atualizar_interface()
    botao_desfazer.on('click', desfazer)

    def refazer(_=None):
        if ed['futuro']:
            ed['historico'].append(ed['texto_atual'])
            proximo = ed['futuro'].pop()
            ed['texto_atual'] = proximo
            _repor_valor_editor(proximo)
            atualizar_interface()
    botao_refazer.on('click', refazer)

    def recarregar(_=None):
        def confirmar_recarregar():
            definir_conteudo(ed['texto_original'])
            ed['historico'].clear()
            ed['futuro'].clear()
            ui.notify('XML recarregado ao estado processado automaticamente.', type='info')
            dialogo_recarregar.close()

        # Só interrompe com uma confirmação se houver algo de fato a perder;
        # se o texto já está igual ao original, recarrega direto sem incomodar.
        if ed['texto_atual'] == ed['texto_original']:
            ui.notify('Nada para recarregar — o editor já está no estado original.', type='info')
            return

        with ui.dialog() as dialogo_recarregar, ui.card():
            ui.label('Descartar alterações?').classes('text-base font-bold')
            ui.label('Isso vai descartar todas as edições feitas neste XML desde o processamento '
                      'automático, voltando ao estado original. Essa ação não pode ser desfeita.') \
                .classes('text-sm text-gray-600')
            with ui.row().classes('w-full justify-end gap-2 mt-2'):
                ui.button('Cancelar', on_click=dialogo_recarregar.close).props('flat')
                ui.button('Descartar e recarregar', color='negative', on_click=confirmar_recarregar)
        dialogo_recarregar.open()
    botao_recarregar.on('click', recarregar)

    def validar(_=None):
        try:
            ed['texto_atual'].encode('ISO-8859-1')
            ET.fromstring(ed['texto_atual'].encode('ISO-8859-1'))
            ui.notify('✓ XML válido', type='positive')
        except Exception as e:
            ui.notify(f'✕ XML inválido: {e}', type='negative')
    botao_validar.on('click', validar)

    def baixar(_=None):
        ui.download.content(resultado['xml_bytes'], f"PRONTO_{nome_arquivo}", media_type='application/xml')
    botao_baixar.on('click', baixar)

    def copiar(_=None):
        ui.run_javascript(f"navigator.clipboard.writeText({ed['texto_atual']!r})")
        ui.notify('Código copiado para a área de transferência.', type='positive')
    botao_copiar.on('click', copiar)

    def localizar(_=None):
        termo = campo_localizar.value
        if not termo:
            resultado_busca.text = 'Informe o texto a localizar.'
            return
        qtd = ed['texto_atual'].count(termo)
        resultado_busca.text = f'{qtd} ocorrência(s) encontrada(s).'
    botao_loc.on('click', localizar)

    def substituir_um(_=None):
        termo, novo = campo_localizar.value, campo_substituir.value
        if not termo:
            resultado_busca.text = 'Informe o texto a localizar.'
            return
        pos = ed['texto_atual'].find(termo)
        if pos == -1:
            resultado_busca.text = 'Nenhuma ocorrência encontrada.'
            return
        texto = ed['texto_atual']
        definir_conteudo(texto[:pos] + novo + texto[pos + len(termo):])
        resultado_busca.text = '1 ocorrência substituída.'
    botao_sub_um.on('click', substituir_um)

    def substituir_todos(_=None):
        termo, novo = campo_localizar.value, campo_substituir.value
        if not termo:
            resultado_busca.text = 'Informe o texto a localizar.'
            return
        qtd = ed['texto_atual'].count(termo)
        definir_conteudo(ed['texto_atual'].replace(termo, novo))
        resultado_busca.text = f'{qtd} ocorrência(s) substituída(s).'
        menu_localizar.close()
    botao_sub_todos.on('click', substituir_todos)

    atualizar_interface()


ui.run(
    title='Validador e Corretor XML Unimed',
    port=int(os.environ.get('PORT', 8080)),
    reload=False,
    show=False,  # não há navegador local para abrir num servidor publicado
    # Em produção, defina a variável de ambiente STORAGE_SECRET com um valor
    # aleatório e secreto. Sem isso, é gerado um novo a cada reinício (o que
    # significa que sessões de navegador abertas antes de um redeploy perdem
    # o estado — aceitável para esta aplicação, mas configure STORAGE_SECRET
    # se quiser evitar isso).
    storage_secret=os.environ.get('STORAGE_SECRET') or secrets.token_hex(16),
)
