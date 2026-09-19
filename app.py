# ==========================================================================
# VALIDADOR TISS — Versão NiceGUI (migrada do Streamlit)
# ==========================================================================
# Reaproveita, sem nenhuma alteração de lógica, as mesmas funções de
# negócio já validadas na versão Streamlit (processar_xml_tiss, cálculo
# oficial de hash da ANS, todas as regras de correção). A camada de
# interface foi refeita do zero em NiceGUI.
#
# Arquivos necessários na MESMA pasta deste script:
#   - credentials.json  -> chave de Service Account do Google (leitura E
#                           escrita — precisa de permissão de Editor na
#                           planilha, não só Leitor)
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
from nicegui import ui

# ==========================================
# NAMESPACES E HELPERS TISS (idêntico à versão Streamlit)
# ==========================================
NS = {'ans': 'http://www.ans.gov.br/padroes/tiss/schemas'}

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

def padronizar_codigo_8_digitos(cod):
    c = limpar_numero(cod)
    return "0" + c if len(c) == 7 and c.isdigit() else c


# ==========================================
# ESTRUTURA PADRÃO DAS TABELAS DE REGRAS (idêntico à versão Streamlit)
# ==========================================
tabelas_padrao = {
    'troca_equipe_sadt': pd.DataFrame(columns=['Nome Original (Erro)', 'Nome Novo', 'CRM Novo', 'CBO Novo', 'Cód Operadora Novo', 'Grau Part Novo', 'Conselho Novo', 'UF Nova']),
    'medicos': pd.DataFrame(columns=['Nome do Médico', 'CBO Correto', 'Substituir por Cód. Operadora', 'Código na Operadora']),
    'procedimentos': pd.DataFrame(columns=['Código do Procedimento', 'Grau Part Obrigatório', 'Via de Acesso (1, 2 ou EXCLUIR)', 'Técnica (1, 2 ou EXCLUIR)']),
    'conveniados': pd.DataFrame(columns=['Nome do Médico Conveniado']),
    'blindagem': pd.DataFrame(columns=['Código Prestador Protegido']),
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
# ACESSO AO GOOGLE SHEETS (leitura E escrita, via Service Account)
# Substitui o st.connection("gsheets", ...) do Streamlit — aqui a app não
# roda dentro do Streamlit, então falamos com a planilha diretamente via
# gspread. Se as credenciais não estiverem configuradas, a aplicação
# continua funcionando normalmente, só sem nenhuma regra pré-carregada
# (você recebe um aviso, não um erro fatal).
# ==========================================
PASTA_SCRIPT = os.path.dirname(os.path.abspath(__file__))
CREDENCIAIS_PATH = os.path.join(PASTA_SCRIPT, "credentials.json")
CONFIG_PATH = os.path.join(PASTA_SCRIPT, "config.json")
_SCOPES_SHEETS = ["https://www.googleapis.com/auth/spreadsheets"]

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

def salvar_tabela_no_sheets(aba, df):
    """Grava o DataFrame inteiro na aba correspondente do Google Sheets
    (substitui o conteúdo existente). Retorna (sucesso, mensagem_de_erro)."""
    sh, erro_conexao = _conectar_planilha()
    if sh is None:
        return False, erro_conexao or "Conexão com o Google Sheets não configurada."
    try:
        ws = sh.worksheet(aba)
        ws.clear()
        valores = [df.columns.astype(str).tolist()] + df.astype(str).values.tolist()
        ws.update(valores)
        return True, None
    except Exception as e:
        return False, str(e)


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

def processar_xml_tiss(arquivo_xml, dfs):
    auditoria = {
        'cbos': [], 'medicos_trocados': [], 'itens': [], 'anvisa': [], 'unidades': [], 'oxigenio': [],
        'conveniados_excluidos': [], 'procedimentos_ajustados': [], 'guias_blindadas': [], 'erros': [],
        'valores_negativos': [], 'motivo_encerramento': [], 'horarios_duplicados': []
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
    set_blindagem = set(df_blindagem['Código Prestador Protegido'].apply(limpar_numero).dropna()) if not df_blindagem.empty and 'Código Prestador Protegido' in df_blindagem.columns else set()

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
                eh_unimed_0014 = numero_carteira.startswith('0014')

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
                        
                        grau_val = limpar_numero(regra_p.get('Grau Part Obrigatório', ''))
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

            # --- OUTRAS DESPESAS ---
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

    return xml_bytes, auditoria

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
    'horarios_duplicados': '⏰ Horários Escalonados (Anti-Duplicidade)'
}


# ==========================================
# TEMA VISUAL (mesmo espírito "desktop corporativo" da versão Streamlit)
# ==========================================
ui.add_head_html("""
<style>
    body { background-color: #f5f6f8 !important; }
    .tiss-header, .tiss-toolbar, .tiss-statusbar, .tiss-panel {
        background-color: #ffffff;
        border: 1px solid #d1d5db;
        border-radius: 4px;
    }
    .tiss-header { padding: 8px 14px; }
    .tiss-toolbar { padding: 4px 8px; }
    .tiss-statusbar { padding: 6px 14px; font-size: 12.5px; color: #374151; }
    .tiss-panel { padding: 10px; height: 74vh; overflow-y: auto; }
    .tiss-app-name { font-weight: 700; color: #111827; font-size: 15px; }
    .tiss-file-name { font-weight: 600; color: #374151; margin-left: 10px; }
    .tiss-file-name.modificado { color: #b45309; }
    .diff-item { border-left: 3px solid #d97706; background-color: #fffbeb;
                 padding: 6px 8px; margin-bottom: 6px; border-radius: 2px; font-size: 12.5px; }
    .diff-linha { color: #92400e; font-weight: 700; font-size: 11px; }
    .diff-campo { color: #1f2937; font-weight: 600; }
    .diff-valores { color: #4b5563; font-family: 'Consolas', monospace; font-size: 11.5px; }
</style>
""", shared=True)


@ui.page('/')
def pagina_principal():
    # ======================================================================
    # ESTADO DESTA SESSÃO/ABA DO NAVEGADOR — cada usuário que abrir a
    # aplicação recebe seu próprio dicionário 'estado', isolado dos demais
    # (importante: os arquivos e edições de uma pessoa NUNCA aparecem para
    # outra, já que isso vai ser publicado para múltiplos usuários).
    # ======================================================================
    dfs_iniciais, avisos_sheets = carregar_tabelas_do_sheets()
    estado = {
        'dfs': dfs_iniciais,
        'arquivos_pendentes': [],   # [(nome, bytes), ...] aguardando processamento
        'resultados_lote': [],
        'lote_id': 0,
    }
    editores = {}  # chave: (lote_id, nome_arquivo) -> dict com o estado do editor daquele arquivo

    with ui.tabs().classes('w-full') as abas_principais:
        aba_processar = ui.tab('📜 Processar XMLs')
        aba_regras = ui.tab('🛠️ Parametrização e Regras de Negócio')

    with ui.tab_panels(abas_principais, value=aba_processar).classes('w-full'):
        with ui.tab_panel(aba_processar):
            if avisos_sheets:
                with ui.expansion('⚠️ Avisos ao carregar as regras do Google Sheets', icon='warning').classes('w-full mb-2'):
                    for a in avisos_sheets:
                        ui.label(f"• {a}").classes('text-sm text-amber-700')
            construir_aba_processamento(estado, editores)

        with ui.tab_panel(aba_regras):
            construir_aba_regras(estado)


# ==========================================================================
# ABA "PROCESSAR XMLs"
# ==========================================================================
def construir_aba_processamento(estado, editores):

    def ao_receber_upload(e):
        conteudo = e.file.read()
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
                    xml_resultado, auditoria = processar_xml_tiss(io.BytesIO(conteudo), estado['dfs'])
                    resultado['xml_bytes'] = xml_resultado
                    resultado['auditoria'] = auditoria
                except Exception as e:
                    resultado['falha_total'] = str(e)
                resultados.append(resultado)
                barra.set_value((i + 1) / len(pendentes))
            estado['resultados_lote'] = resultados
            estado['lote_id'] += 1
            estado['arquivos_pendentes'] = []
            label_pendentes.text = 'Nenhum arquivo selecionado ainda.'
            barra.visible = False
            painel_resultados.refresh()

        ui.button('🚀 Iniciar Correção Automática', on_click=iniciar_correcao, color='primary').classes('w-full mt-2')
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
        if len(sucesso) > 1:
            def baixar_zip():
                buffer = io.BytesIO()
                with zipfile.ZipFile(buffer, 'w', zipfile.ZIP_DEFLATED) as zf:
                    for r in sucesso:
                        zf.writestr(f"PRONTO_{r['nome']}", r['xml_bytes'])
                ui.download.content(buffer.getvalue(), 'XMLS_CORRIGIDOS.zip', media_type='application/zip')
            ui.button('📦 Baixar Todos os XMLs Corrigidos (.ZIP)', on_click=baixar_zip, color='primary').classes('w-full')
            seletor_arquivo = ui.select(nomes, value=nomes[0], label='Arquivo selecionado').classes('w-full mt-2')
        else:
            seletor_arquivo = None

        nome_escolhido = seletor_arquivo.value if seletor_arquivo else nomes[0]
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

        if seletor_arquivo:
            seletor_arquivo.on_value_change(lambda: painel_resultados.refresh())

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
        xml_texto = resultado['xml_bytes'].decode('ISO-8859-1')
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
        }
    ed = editores[chave]

    def definir_conteudo(novo_texto, empilhar_undo=True):
        if empilhar_undo:
            ed['historico'].append(ed['texto_atual'])
            ed['historico'][:] = ed['historico'][-50:]
            ed['futuro'].clear()
        ed['texto_atual'] = novo_texto
        editor.set_value(novo_texto)
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
                editor = ui.codemirror(value=ed['texto_atual'], language='XML', theme='basicLight') \
                    .classes('w-full h-full border').style('font-size: 13px')
            with ui.column().classes('gap-0 tiss-panel').style('flex: 1; min-width: 260px'):
                ui.label('ALTERAÇÕES').classes('font-bold text-sm mb-1')
                painel_alteracoes = ui.column().classes('w-full gap-0')

        with ui.row().classes('w-full items-center tiss-statusbar gap-6'):
            status_arquivo = ui.label()
            status_validade = ui.label()
            status_linhas = ui.label()
            status_alteracoes = ui.label()
            status_hash = ui.html()

        with ui.expander('📝 Ver Detalhes das Modificações Automáticas').classes('w-full'):
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
    def atualizar_interface():
        alterado = ed['texto_atual'] != ed['texto_base']
        label_arquivo.text = f"{nome_arquivo} *" if alterado else nome_arquivo
        label_arquivo.classes(replace='tiss-file-name modificado' if alterado else 'tiss-file-name')

        botao_salvar_header.props(f"{'disable' if not alterado else ''}")
        botao_desfazer.props(f"{'disable' if not ed['historico'] else ''}")
        botao_refazer.props(f"{'disable' if not ed['futuro'] else ''}")

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

        try:
            ET.fromstring(ed['texto_atual'].encode('ISO-8859-1'))
            status_validade.text = '✓ XML válido'
            status_validade.classes(replace='text-green-700 font-semibold')
        except Exception:
            status_validade.text = '✕ XML inválido'
            status_validade.classes(replace='text-red-700 font-semibold')

        status_arquivo.text = html.escape(nome_arquivo)
        status_linhas.text = f"{len(ed['texto_atual'].splitlines())} linhas"
        status_alteracoes.text = (f"⚠ {len(alteracoes)} alteração(ões) não salva(s)" if alterado
                                   else ("💾 Alterações salvas" if ed['salvo_alguma_vez'] else "Sem alterações"))
        status_alteracoes.classes(replace='text-amber-700 font-semibold' if alterado else 'text-gray-600')

        hash_dif = ed['hash_atual'] != ed['hash_original']
        cor = 'color:#b45309;font-weight:600' if hash_dif else 'color:#374151'
        status_hash.content = (f"Hash original: <code>{ed['hash_original'] or '—'}</code> &nbsp;|&nbsp; "
                                f"<span style='{cor}'>Hash atual: <code>{ed['hash_atual'] or '—'}</code></span>")

    # ---------------- Eventos ----------------
    def ao_digitar(e):
        ed['texto_atual'] = e.value
        atualizar_interface()
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
        ui.notify('✅ Alterações salvas e hash recalculado.', type='positive')
    botao_salvar_header.on('click', salvar)

    def desfazer(_=None):
        if ed['historico']:
            ed['futuro'].append(ed['texto_atual'])
            anterior = ed['historico'].pop()
            ed['texto_atual'] = anterior
            editor.set_value(anterior)
            atualizar_interface()
    botao_desfazer.on('click', desfazer)

    def refazer(_=None):
        if ed['futuro']:
            ed['historico'].append(ed['texto_atual'])
            proximo = ed['futuro'].pop()
            ed['texto_atual'] = proximo
            editor.set_value(proximo)
            atualizar_interface()
    botao_refazer.on('click', refazer)

    def recarregar(_=None):
        definir_conteudo(ed['texto_original'])
        ed['historico'].clear()
        ed['futuro'].clear()
        ui.notify('XML recarregado ao estado processado automaticamente.', type='info')
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


# ==========================================================================
# ABA "PARAMETRIZAÇÃO E REGRAS DE NEGÓCIO"
# ==========================================================================
_ROTULOS_ABAS_REGRAS = {
    'medicos': '👨‍⚕️ Médicos',
    'procedimentos': '⚙️ Procedimentos',
    'troca_equipe_sadt': '🔀 Troca de Equipe SADT',
    'conveniados': '🤝 Conveniados',
    'blindagem': '🛡️ Blindagem',
    'itens': '📦 Itens',
    'unidades': '📏 Unidades de Medida',
    'anvisa': '🩺 ANVISA',
}

def construir_aba_regras(estado):
    with ui.row().classes('w-full justify-end'):
        def recarregar_tudo():
            estado['dfs'], avisos = carregar_tabelas_do_sheets()
            if avisos:
                ui.notify('Recarregado com avisos — veja o console/expander no topo.', type='warning')
            else:
                ui.notify('Regras recarregadas do Google Sheets.', type='positive')
            abas_regras.refresh()
        ui.button('🔄 Recarregar do Google Sheets', on_click=recarregar_tudo).props('flat')

    abas_regras(estado)


@ui.refreshable
def abas_regras(estado):
    with ui.tabs().classes('w-full') as sub_abas:
        objetos_aba = {aba: ui.tab(_ROTULOS_ABAS_REGRAS.get(aba, aba)) for aba in tabelas_padrao.keys()}

    with ui.tab_panels(sub_abas, value=objetos_aba['medicos']).classes('w-full'):
        for aba, tab_obj in objetos_aba.items():
            with ui.tab_panel(tab_obj):
                construir_tabela_regra(estado, aba)


def construir_tabela_regra(estado, aba):
    df = estado['dfs'].get(aba, tabelas_padrao[aba]).copy()
    if df.empty:
        df = pd.DataFrame(columns=tabelas_padrao[aba].columns)
        df.loc[0] = [''] * len(df.columns)

    colunas = [{'headerName': c, 'field': c, 'editable': True, 'flex': 1} for c in df.columns]
    grid = ui.aggrid({
        'columnDefs': colunas,
        'rowData': df.to_dict('records'),
        'rowSelection': 'multiple',
        'stopEditingWhenCellsLoseFocus': True,
    }).classes('w-full h-96')

    def adicionar_linha():
        nova = {c: '' for c in df.columns}
        grid.options['rowData'].append(nova)
        grid.update()

    async def remover_selecionadas():
        selecionadas = await grid.get_selected_rows()
        if not selecionadas:
            ui.notify('Selecione ao menos uma linha (clique na linha, não só na célula).', type='warning')
            return
        grid.options['rowData'] = [r for r in grid.options['rowData'] if r not in selecionadas]
        grid.update()

    async def salvar_na_nuvem():
        dados_atuais = await grid.get_client_data()
        novo_df = pd.DataFrame(dados_atuais)
        # remove linhas totalmente vazias antes de gravar
        novo_df = novo_df[~(novo_df.astype(str).apply(lambda col: col.str.strip()).eq('').all(axis=1))]
        sucesso, erro = salvar_tabela_no_sheets(aba, novo_df)
        if sucesso:
            estado['dfs'][aba] = formatar_tabela_padrao(novo_df.copy())
            ui.notify(f"✅ Regras de '{_ROTULOS_ABAS_REGRAS.get(aba, aba)}' gravadas na nuvem.", type='positive')
        else:
            ui.notify(f"❌ Falha ao gravar: {erro}", type='negative', multi_line=True, close_button=True)

    with ui.row().classes('w-full gap-2 mt-2'):
        ui.button('➕ Adicionar Linha', on_click=adicionar_linha).props('flat')
        ui.button('🗑️ Remover Selecionadas', on_click=remover_selecionadas).props('flat')
        ui.button('💾 Gravar Alterações na Nuvem', on_click=salvar_na_nuvem, color='primary')


ui.run(
    title='Validador TISS',
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
