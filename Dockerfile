# Dockerfile para publicar o Validador TISS (NiceGUI) num serviço de nuvem.
FROM python:3.12-slim

WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY app_unimed_nicegui.py .
# NÃO copie credentials.json/config.json aqui — eles NUNCA devem entrar no
# repositório. No Render, credentials.json chega via "Secret File" (montado
# automaticamente em /etc/secrets/credentials.json) e o link da planilha via
# variável de ambiente SPREADSHEET_URL. O código já sabe procurar nesses
# dois lugares.

EXPOSE 8080

CMD ["python", "app_unimed_nicegui.py"]
