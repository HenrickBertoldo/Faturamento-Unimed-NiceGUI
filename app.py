import hashlib
import re
import zipfile
import traceback
import difflib
import html
import xml.etree.ElementTree as ET
import pandas as pd
import io
from datetime import datetime, timedelta

from nicegui import ui, events, app

# ==========================================
# CONSTANTES E NAMESPACES TISS
# ==========================================
NS = {'ans': 'http://www.ans.gov.br/padroes/tiss/schemas'}
for k, v in NS.items():
    ET.register_namespace(k, v)
ET.register_namespace('xsi', 'http://www.w3.org/2001/XMLSchema-instance')

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

# ==========================================
# ESTRUTURA PADRÃO DAS TABELAS E ESTADO
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

class AppState:
    def __init__(self):
        self.dfs = {k: formatar_tabela_padrao(v.copy()) for k, v in tabelas_padrao.items()}
        self.resultados_lote = []
        self.forcar_upload_aberto = False
        self.editor_state = {}

app_state = AppState()

# Funções simuladas do Google Sheets (No NiceGUI, você deve usar gspread ou pandas para ler URLs públicas)
def carregar_do_sheets(silencioso=False):
    try:
        # Substitua este bloco pela lógica real do gspread ou pandas.read_csv()
        for aba in tabelas_padrao.keys():
            if app_state.dfs[aba].empty:
                app_state.dfs[aba] = formatar_tabela_padrao(tabelas_padrao[aba].copy())
        if not silencioso: ui.notify("✅ Regras sincronizadas (Simulação)", type='positive')
    except Exception as e:
        if not silencioso:
            ui.notify(f"Erro na conexão: {e}", type='negative')

def salvar_no_sheets():
    try:
        # Substitua este bloco por lógica de escrita via gspread
        ui.notify("✅ Alterações gravadas na nuvem (Simulação)", type='positive')
    except Exception as e:
        ui.notify(f"Erro ao salvar: {e}", type='negative')

# ==========================================
# MOTOR DE CORREÇÃO DO XML REVISADO 
# ==========================================
def calcular_tempo_oxigenio(hora_ini_str, qtd_executada, tipo_unidade):
    try:
        qtd = float(qtd_executada.strip())
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

def padronizar_codigo_8_digitos(cod):
    c = limpar_numero(cod)
    return "0" + c if len(c) == 7 and c.isdigit() else c

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
    if 'valores_negativos' not in auditoria: auditoria['valores_negativos'] = []
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
    if 'motivo_encerramento' not in auditoria: auditoria['motivo_encerramento'] = []
    auditoria['motivo_encerramento'].extend(logs)
    return len(logs)

def _somar_segundos(hora_str, segundos):
    t = datetime.strptime(hora_str.strip(), "%H:%M:%S")
    return (t + timedelta(seconds=segundos)).strftime("%H:%M:%S")

def calcular_hash_tiss(root, hash_node):
    partes = []
    for elem in root.iter():
        if elem is hash_node: continue
        if len(list(elem)) > 0: continue
        texto = elem.text
        if texto is None or texto.strip() == '': continue
        partes.append(texto)
    concatenado = ''.join(partes)
    return hashlib.md5(concatenado.encode('ISO-8859-1')).hexdigest()

def ajustar_horarios_duplicados(procs_container, auditoria):
    if 'horarios_duplicados' not in auditoria: auditoria['horarios_duplicados'] = []
    grupos = {}
    for proc_exec in procs_container.findall('ans:procedimentoExecutado', NS):
        cod_elem = proc_exec.find('.//ans:codigoProcedimento', NS)
        data_elem = proc_exec.find('ans:dataExecucao', NS)
        h_ini_elem = proc_exec.find('ans:horaInicial', NS)
        h_fim_elem = proc_exec.find('ans:horaFinal', NS)
        if cod_elem is None or data_elem is None or h_ini_elem is None or h_fim_elem is None: continue
        if not (cod_elem.text and data_elem.text and h_ini_elem.text and h_fim_elem.text): continue
        chave = (padronizar_codigo_8_digitos(cod_elem.text), data_elem.text.strip(), h_ini_elem.text.strip(), h_fim_elem.text.strip())
        grupos.setdefault(chave, []).append((h_ini_elem, h_fim_elem))
    for (cod_p, data_exec, h_ini_orig, h_fim_orig), ocorrencias in grupos.items():
        if len(ocorrencias) < 2: continue
        for i, (h_ini_elem, h_fim_elem) in enumerate(ocorrencias[1:], start=1):
            h_ini_elem.text = _somar_segundos(h_ini_orig, i)
            h_fim_elem.text = _somar_segundos(h_fim_orig, i)
        auditoria['horarios_duplicados'].append(f"Procedimento {cod_p} em {data_exec}: {len(ocorrencias)} ocorrências escalonadas.")

def recalcular_hash_e_serializar(tree, root):
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

def validar_e_recalcular_xml_editado(texto_editado):
    try:
        xml_encodado = texto_editado.encode('ISO-8859-1')
    except UnicodeEncodeError as e:
        return None, f"O texto contém um caractere fora do padrão ISO-8859-1 (posição {e.start})."
    try:
        root = ET.fromstring(xml_encodado)
    except ET.ParseError as e:
        return None, f"XML inválido: {e}"
    tree = ET.ElementTree(root)
    try:
        xml_bytes = recalcular_hash_e_serializar(tree, root)
    except Exception as e:
        return None, f"Falha ao recalcular o hash/serializar: {e}"
    return xml_bytes, None

def _extrair_hash_do_texto(texto):
    m = re.search(r'<ans:hash>([^<]*)</ans:hash>', texto)
    return m.group(1).strip() if m else None

_PADRAO_TAG_LINHA = re.compile(r'<([\w:.-]+)>([^<]*)</\1>')

def calcular_diff_alteracoes(texto_base, texto_atual):
    linhas_base = texto_base.splitlines()
    linhas_atual = texto_atual.splitlines()
    sm = difflib.SequenceMatcher(None, linhas_base, linhas_atual)
    alteracoes = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal': continue
        antigas = linhas_base[i1:i2]
        novas = linhas_atual[j1:j2]
        pares = list(zip(antigas, novas)) if len(antigas) == len(novas) else []
        if pares:
            for offset, (linha_antiga, linha_nova) in enumerate(pares):
                if linha_antiga == linha_nova: continue
                m_antiga = _PADRAO_TAG_LINHA.search(linha_antiga)
                m_nova = _PADRAO_TAG_LINHA.search(linha_nova)
                numero_linha = j1 + offset + 1
                if m_antiga and m_nova and m_antiga.group(1) == m_nova.group(1):
                    alteracoes.append({'linha': numero_linha, 'campo': m_antiga.group(1), 'antes': m_antiga.group(2), 'depois': m_nova.group(2)})
                else:
                    alteracoes.append({'linha': numero_linha, 'campo': None, 'antes': linha_antiga.strip(), 'depois': linha_nova.strip()})
        else:
            numero_linha = j1 + 1 if novas else i1 + 1
            alteracoes.append({'linha': numero_linha, 'campo': None, 'antes': ' / '.join(l.strip() for l in antigas) if antigas else '(nada)', 'depois': ' / '.join(l.strip() for l in novas) if novas else '(removido)'})
    return alteracoes

def processar_xml_tiss(arquivo_bytes, arquivo_nome, dfs):
    auditoria = {
        'cbos': [], 'medicos_trocados': [], 'itens': [], 'anvisa': [], 'unidades': [], 'oxigenio': [],
        'conveniados_excluidos': [], 'procedimentos_ajustados': [], 'guias_blindadas': [], 'erros': [],
        'valores_negativos': [], 'motivo_encerramento': [], 'horarios_duplicados': []
    }
    
    arquivo_bytes.seek(0)
    tree = ET.parse(arquivo_bytes)
    root = tree.getroot()

    corrigir_valores_negativos(root, auditoria)
    corrigir_motivo_encerramento(root, auditoria)

    df_medicos = dfs.get('medicos', pd.DataFrame())
    dict_medicos = {str(r.get('Nome do Médico', '')).strip().upper(): r for _, r in df_medicos.iterrows() if str(r.get('Nome do Médico', '')).strip().upper() not in ['NAN', 'NONE', '<NA>', '']}
    
    df_equipe_sadt = dfs.get('troca_equipe_sadt', pd.DataFrame())
    dict_equipe_sadt = {str(r.get('Nome Original (Erro)', '')).strip().upper(): {
        'nome_novo': str(r.get('Nome Novo', '')).strip(), 'crm_novo': limpar_numero(r.get('CRM Novo', '')),
        'cbo_novo': limpar_numero(r.get('CBO Novo', '')), 'cod_op_novo': limpar_numero(r.get('Cód Operadora Novo', '')),
        'grau_novo': limpar_numero(r.get('Grau Part Novo', '')), 'conselho_novo': limpar_numero(r.get('Conselho Novo', '')),
        'uf_nova': limpar_numero(r.get('UF Nova', ''))
    } for _, r in df_equipe_sadt.iterrows() if str(r.get('Nome Original (Erro)', '')).strip().upper() not in ['NAN', 'NONE', '<NA>', '']}

    df_conveniados = dfs.get('conveniados', pd.DataFrame())
    set_conveniados = set(df_conveniados['Nome do Médico Conveniado'].dropna().astype(str).str.strip().str.upper()) if 'Nome do Médico Conveniado' in df_conveniados.columns else set()

    df_blindagem = dfs.get('blindagem', pd.DataFrame())
    set_blindagem = set(df_blindagem['Código Prestador Protegido'].apply(limpar_numero).dropna()) if 'Código Prestador Protegido' in df_blindagem.columns else set()

    df_itens = dfs.get('itens', pd.DataFrame())
    dict_itens = {padronizar_codigo_8_digitos(k): padronizar_codigo_8_digitos(v) for k, v in zip(df_itens['Código Incorreto'], df_itens['Código Correto']) if pd.notna(k)} if 'Código Incorreto' in df_itens.columns else {}

    df_unidades = dfs.get('unidades', pd.DataFrame())
    dict_unidades = {padronizar_codigo_8_digitos(r['Código do Item']): limpar_numero(r['Unidade de Medida Correta']) for _, r in df_unidades.iterrows() if pd.notna(r.get('Código do Item'))} if 'Código do Item' in df_unidades.columns else {}

    df_anvisa = dfs.get('anvisa', pd.DataFrame())
    dict_anvisa = {padronizar_codigo_8_digitos(r['Código do Item']): r for _, r in df_anvisa.iterrows() if pd.notna(r.get('Código do Item'))} if 'Código do Item' in df_anvisa.columns else {}

    df_procedimentos = dfs.get('procedimentos', pd.DataFrame())
    dict_procedimentos = {padronizar_codigo_8_digitos(r['Código do Procedimento']): r for _, r in df_procedimentos.iterrows() if pd.notna(r.get('Código do Procedimento'))} if 'Código do Procedimento' in df_procedimentos.columns else {}

    todas_guias = [(g, 'internacao') for g in root.findall('.//ans:guiaResumoInternacao', NS)] + [(g, 'sadt') for g in root.findall('.//ans:guiaSP-SADT', NS)]

    for indice_guia, (guia, tipo_guia) in enumerate(todas_guias, start=1):
        try:
            prestador_elem = guia.find('.//ans:dadosPrestador/ans:codigoPrestadorNaOperadora', NS)
            if prestador_elem is None: prestador_elem = guia.find('.//ans:dadosContratado/ans:codigoPrestadorNaOperadora', NS)
            if prestador_elem is not None and limpar_numero(prestador_elem.text) in set_blindagem:
                auditoria['guias_blindadas'].append(f"Guia ignorada (Prestador {limpar_numero(prestador_elem.text)} protegido)")
                continue

            carteira_elem = guia.find('.//ans:dadosBeneficiario/ans:numeroCarteira', NS)
            numero_carteira = limpar_numero(carteira_elem.text) if carteira_elem is not None and carteira_elem.text else ""
            eh_unimed_0014 = numero_carteira.startswith('0014')

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
                            auditoria['medicos_trocados'].append(f"Guia SADT (Equipe Completa): Mapeamento de '{nome_orig_xml}' substituído.")

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
                        if tipo_guia == 'internacao' and eh_unimed_0014 and nome_prof in set_conveniados and not is_protected:
                            equipes_remover.append(eq)
                            auditoria['conveniados_excluidos'].append(f"Removido médico(a) '{nome_prof}' do procedimento {cod_p}")
                    for eq in equipes_remover: proc_exec.remove(eq)
                    
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
                        def _normaliza_via_tecnica(valor): return str(int(valor)) if valor.isdigit() else valor

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

                    for eq in equipes_restantes:
                        nome_prof_elem = eq.find('.//ans:nomeProf', NS)
                        nome_prof = nome_prof_elem.text.strip().upper() if nome_prof_elem is not None and nome_prof_elem.text else ""
                        if nome_prof in set_conveniados: continue 
                        if nome_prof in dict_medicos:
                            regra_m = dict_medicos[nome_prof]
                            cbo_novo = limpar_numero(regra_m.get('CBO Correto', ''))
                            target_node = eq if tag_limpa(eq) == 'equipeSadt' else (eq.find('ans:identificacaoEquipe', NS) or eq)
                            cbos_existentes = [elem for elem in eq.iter() if tag_limpa(elem) in ['CBOS', 'codigoCBOS', 'codigoCBO']]

                            if cbo_novo != '':
                                if cbos_existentes:
                                    primeiro_cbo = cbos_existentes[0]
                                    if primeiro_cbo.text != cbo_novo:
                                        primeiro_cbo.text = cbo_novo
                                        auditoria['cbos'].append(f"Médico(a) '{nome_prof}': CBO alterado para {cbo_novo}")
                                    for c_extra in cbos_existentes[1:]:
                                        for parent in eq.iter():
                                            if c_extra in list(parent): parent.remove(c_extra)
                                else:
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
                ajustar_horarios_duplicados(procs_container, auditoria)

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
                                        auditoria['oxigenio'].append(f"Oxigênio {cod_item}: Hora ajustada para {h_ini_novo} / {h_fim_novo}")
                                    h_ini.text = h_ini_novo
                                    h_fim.text = h_fim_novo
                                else:
                                    auditoria['erros'].append(f"Item {cod_item}: não foi possível recalcular hora")

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
                                auditoria['anvisa'].append(f"Item {cod_item}: Inserido ANVISA/Ref")

        except Exception as e:
            auditoria['erros'].append(f"Guia #{indice_guia} ({tipo_guia}): erro ao processar — {e}")

    xml_bytes = recalcular_hash_e_serializar(tree, root)
    return xml_bytes, auditoria

# ==========================================
# INTERFACE GRÁFICA NICEGUI
# ==========================================
ui.add_css("""
    .tiss-header { display: flex; align-items: center; justify-content: space-between; background-color: #f3f4f6; border: 1px solid #d1d5db; border-radius: 4px; padding: 0.5rem 0.9rem; margin-bottom: 0.5rem; }
    .tiss-header .app-name { font-weight: 700; font-size: 0.95rem; color: #1f2937; }
    .tiss-header .file-name { font-weight: 600; font-size: 0.95rem; color: #374151; margin-left: 0.6rem; }
    .tiss-header .file-name.modificado { color: #b45309; }
    .tiss-statusbar { display: flex; gap: 1.4rem; align-items: center; background-color: #f3f4f6; border: 1px solid #d1d5db; border-radius: 4px; padding: 0.35rem 0.9rem; font-size: 0.82rem; color: #374151; margin-top: 0.4rem; }
    .tiss-statusbar .ok { color: #15803d; font-weight: 600; }
    .tiss-statusbar .erro { color: #b91c1c; font-weight: 600; }
    .tiss-statusbar .alterado { color: #b45309; font-weight: 600; }
    .tiss-diff-item { border-left: 3px solid #d97706; background-color: #fffbeb; padding: 0.35rem 0.5rem; margin-bottom: 0.4rem; border-radius: 2px; font-size: 0.8rem; }
    .tiss-diff-item .linha { color: #92400e; font-weight: 700; font-size: 0.75rem; }
    .tiss-diff-item .campo { color: #1f2937; font-weight: 600; }
    .tiss-diff-item .valores { color: #4b5563; font-family: 'Consolas', 'Courier New', monospace; font-size: 0.75rem; }
""")

@ui.page('/')
def index():
    ui.page_title('TISS Cloud')

    ui.label('☁️ Sistema Integrado TISS | UNIMED').classes('text-2xl font-bold')
    ui.label('Automação, correção e validação de faturamento XML em nuvem.').classes('text-sm text-gray-500 mb-4')

    with ui.card().classes('w-full mb-4'):
        ui.label('🔄 Central de Sincronização e Controle de Dados').classes('text-lg font-bold')
        with ui.row().classes('w-full items-end gap-4'):
            with ui.column():
                ui.label('1️⃣ Puxar Configurações').classes('font-bold')
                ui.button('📥 Puxar Regras da Nuvem', on_click=lambda: carregar_do_sheets())
            with ui.column():
                ui.label('2️⃣ Salvar Novas Configurações').classes('font-bold')
                confirm_check = ui.checkbox('Confirmar atualização no Sheets')
                ui.button('💾 Gravar Alterações', on_click=lambda: salvar_no_sheets()).bind_enabled_from(confirm_check, 'value')
            with ui.column():
                ui.label('3️⃣ Carga em Massa (Opcional)').classes('font-bold')
                def handle_excel(e: events.UploadEventArguments):
                    try:
                        xls = pd.read_excel(io.BytesIO(e.content.read()), sheet_name=None, dtype=str)
                        for aba, df_imp in xls.items():
                            if aba in tabelas_padrao:
                                app_state.dfs[aba] = formatar_tabela_padrao(df_imp)
                        ui.notify("Tabelas alimentadas!", type='positive')
                        tabelas_ui.refresh()
                    except Exception as err:
                        ui.notify(f"Erro ao importar: {err}", type='negative')
                ui.upload(label="Upload Excel (.xlsx)", auto_upload=True, on_upload=handle_excel).props('accept=".xlsx, .xls"')

    ui.separator().classes('my-4')

    @ui.refreshable
    def main_workspace():
        tem_resultados = bool(app_state.resultados_lote)
        
        with ui.row().classes('w-full gap-4'):
            # Lado Esquerdo - Upload
            with ui.column().classes('flex-1'):
                titulo = "📁 Trocar arquivos / Novo lote" if tem_resultados else "📜 Processamento de XMLs em Lote"
                with ui.expansion(titulo, value=(not tem_resultados) or app_state.forcar_upload_aberto).classes('w-full bg-gray-50'):
                    ui.label("Arraste um ou vários arquivos XML gerados pelo seu sistema aqui.")
                    
                    def processar_arquivos(e: events.UploadEventArguments):
                        try:
                            arquivo_bytes = io.BytesIO(e.content.read())
                            xml_res, aud = processar_xml_tiss(arquivo_bytes, e.name, app_state.dfs)
                            app_state.resultados_lote.append({'nome': e.name, 'xml_bytes': xml_res, 'auditoria': aud, 'falha_total': None})
                            ui.notify(f"Arquivo {e.name} processado!", type='positive')
                            main_workspace.refresh()
                        except Exception as err:
                            app_state.resultados_lote.append({'nome': e.name, 'falha_total': str(err)})
                            ui.notify(f"Falha em {e.name}: {err}", type='negative')
                            main_workspace.refresh()

                    ui.upload(multiple=True, auto_upload=True, on_upload=processar_arquivos).props('accept=".xml"').classes('w-full')

            # Lado Direito - Resultados
            with ui.column().classes('flex-1'):
                if tem_resultados:
                    with ui.card().classes('w-full'):
                        ui.label("### 📊 Resultado da Auditoria").classes('text-lg font-bold')
                        
                        if len(app_state.resultados_lote) > 1:
                            def baixar_zip():
                                zip_buf = io.BytesIO()
                                with zipfile.ZipFile(zip_buf, "w", zipfile.ZIP_DEFLATED) as zipf:
                                    for res in app_state.resultados_lote:
                                        if res.get('xml_bytes'):
                                            zipf.writestr(f"PRONTO_{res['nome']}", res['xml_bytes'])
                                zip_buf.seek(0)
                                ui.download(zip_buf.getvalue(), "XMLS_CORRIGIDOS.zip")
                            
                            ui.button("📦 Baixar Todos os XMLs Corrigidos (.ZIP)", on_click=baixar_zip).classes('w-full mb-2')
                        
                        res = app_state.resultados_lote[-1] # Exibe o último por padrão na view simplificada
                        if res.get('falha_total'):
                            ui.label(f"❌ {res['nome']}: {res['falha_total']}").classes('text-red-500 font-bold')
                        else:
                            ui.label(f"✅ Arquivo {res['nome']} processado com sucesso!").classes('text-green-600 font-bold')
                            
                            aud = res.get('auditoria', {})
                            with ui.row().classes('w-full justify-between'):
                                ui.label(f"🔀 Médicos Trocados: {len(aud.get('medicos_trocados', []))}")
                                ui.label(f"👩‍⚕️ CBOs / Códs: {len(aud.get('cbos', []))}")
                                ui.label(f"➖ Val Negativos: {len(aud.get('valores_negativos', []))}")
                else:
                    with ui.card().classes('w-full bg-blue-50'):
                        ui.label("Aguardando arquivo(s) XML. Faça o upload na coluna ao lado.")

        if tem_resultados and not app_state.resultados_lote[-1].get('falha_total'):
            render_editor(app_state.resultados_lote[-1])

    def render_editor(resultado):
        nome_arquivo = resultado['nome']
        xml_bytes = resultado['xml_bytes']
        xml_texto = xml_bytes.decode('ISO-8859-1') if isinstance(xml_bytes, bytes) else xml_bytes

        if 'texto_original' not in app_state.editor_state:
            app_state.editor_state = {
                'texto_original': xml_texto, 'texto_atual': xml_texto,
                'hash_orig': _extrair_hash_do_texto(xml_texto), 'hash_atual': _extrair_hash_do_texto(xml_texto)
            }

        st_editor = app_state.editor_state
        alterado = st_editor['texto_atual'] != st_editor['texto_original']

        ui.html(f"""
            <div class="tiss-header mt-6">
                <div><span class="app-name">📄 Validador TISS</span><span class="file-name {'modificado' if alterado else ''}">{nome_arquivo}{' *' if alterado else ''}</span></div>
            </div>
        """)

        with ui.row().classes('w-full mb-2 gap-2'):
            ui.button('📂', on_click=lambda: setattr(app_state, 'forcar_upload_aberto', True) or main_workspace.refresh()).tooltip('Abrir/Novo lote')
            
            def salvar_edicao():
                novos_bytes, erro = validar_e_recalcular_xml_editado(st_editor['texto_atual'])
                if erro:
                    ui.notify(f"❌ {erro}", type='negative')
                else:
                    st_editor['texto_original'] = novos_bytes.decode('ISO-8859-1')
                    st_editor['texto_atual'] = st_editor['texto_original']
                    st_editor['hash_atual'] = _extrair_hash_do_texto(st_editor['texto_atual'])
                    resultado['xml_bytes'] = novos_bytes
                    ui.notify("Salvo com sucesso!", type='positive')
                    main_workspace.refresh()

            ui.button('💾', on_click=salvar_edicao).tooltip('Salvar').bind_enabled_from(st_editor, 'texto_atual', backward=lambda x: x != st_editor['texto_original'])
            
            def recarregar():
                st_editor['texto_atual'] = st_editor['texto_original']
                main_workspace.refresh()
                
            ui.button('⟲ Recarregar', on_click=recarregar).tooltip('Descartar alterações')
            
            ui.button('📥 Baixar XML Atual', on_click=lambda: ui.download(resultado['xml_bytes'], f"PRONTO_{nome_arquivo}"))

        with ui.row().classes('w-full flex-nowrap'):
            with ui.column().classes('w-3/4'):
                def on_editor_change(e):
                    st_editor['texto_atual'] = e.value
                editor = ui.codemirror(value=st_editor['texto_atual'], on_change=on_editor_change).classes('h-[600px] border w-full')
            
            with ui.column().classes('w-1/4 px-2'):
                ui.label("ALTERAÇÕES").classes('font-bold mb-2')
                alteracoes_diff = calcular_diff_alteracoes(st_editor['texto_original'], st_editor['texto_atual']) if alterado else []
                if alteracoes_diff:
                    ui.label(f"🟡 {len(alteracoes_diff)} alteração(ões)")
                    with ui.scroll_area().classes('h-[550px] w-full'):
                        for alt in alteracoes_diff[:60]:
                            ui.html(f"""
                                <div class="tiss-diff-item">
                                    <div class="linha">Linha {alt['linha']}</div>
                                    <div class="campo">{html.escape(alt['campo'] or '(trecho)')}</div>
                                    <div class="valores">{html.escape(alt['antes'])} → {html.escape(alt['depois'])}</div>
                                </div>
                            """)
                else:
                    ui.label("Nenhuma alteração realizada.").classes('text-gray-500 text-sm')

        ui.html(f"""
            <div class="tiss-statusbar">
                <span>{nome_arquivo}</span>
                <span>ISO-8859-1</span>
                <span>{'⚠ Alterado' if alterado else '💾 Salvo'}</span>
                <span>Hash: <code>{st_editor['hash_atual'] or '—'}</code></span>
            </div>
        """)

    main_workspace()

    ui.separator().classes('my-6')

    @ui.refreshable
    def tabelas_ui():
        with ui.card().classes('w-full'):
            ui.label("### 🛠️ Parametrização e Regras de Negócio").classes('text-lg font-bold')
            
            nomes_exibicao = ["🔄 Equipe SADT", "👩‍⚕️ Médicos CBO", "⚙️ Procedimentos", "🤝 Conveniados", "🛡️ Blindagem", "💊 Itens", "📦 Unidades", "🏥 ANVISA"]
            chaves = ['troca_equipe_sadt', 'medicos', 'procedimentos', 'conveniados', 'blindagem', 'itens', 'unidades', 'anvisa']
            
            with ui.tabs() as tabs:
                abas_ui = [ui.tab(n) for n in nomes_exibicao]
            
            with ui.tab_panels(tabs, value=abas_ui[0]).classes('w-full'):
                for aba, chave_tabela in zip(abas_ui, chaves):
                    with ui.tab_panel(aba):
                        df_atual = app_state.dfs[chave_tabela]
                        # NiceGUI AgGrid permite edição direta. 
                        # Atualizamos o dataframe base no callback de edição da grade.
                        grid = ui.aggrid({
                            'columnDefs': [{'field': col, 'editable': True} for col in df_atual.columns],
                            'rowData': df_atual.to_dict('records'),
                            'stopEditingWhenCellsLoseFocus': True
                        }).classes('h-96 w-full')
                        
                        def update_df(e, key=chave_tabela):
                            # Sincroniza dados da grade editável de volta para o DataFrame de estado
                            import json
                            dados = json.loads(e.args['data']) # Dependendo da versão do NiceGUI, pode vir direto no dicionário
                            app_state.dfs[key] = pd.DataFrame(dados)

                        # grid.on('cellValueChanged', update_df) # Evento opcional para auto-save da tabela
    tabelas_ui()

ui.run(title="TISS Cloud", favicon="☁️")
