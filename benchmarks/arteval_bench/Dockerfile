FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

USER root

WORKDIR /
COPY . .

RUN rm -rf /var/lib/apt/lists/* \
 && apt-get update -o Acquire::Retries=5 \
 && apt-get install -y --no-install-recommends \
    build-essential \
    git \
    wget \
    python3-pip \
    python3-venv \
    pipx \
 && rm -rf /var/lib/apt/lists/*

# SWE-ReX will always attempt to install its server into your docker container
# however, this takes a couple of seconds. If we already provide it in the image,
# this is much faster.
RUN pipx install swe-rex 
RUN pipx ensurepath

ENV PATH="/root/.local/bin:${PATH}"
ENV PATH="/usr/local/go/bin:${PATH}"

SHELL ["/bin/bash", "-c"]

RUN chmod +x install.sh test.sh && ./install.sh

# 配置 Claude Agent SDK Bash 超时参数到 ~/.claude/settings.json
# 24小时 = 86400000 毫秒
RUN mkdir -p /root/.claude && \
    cat > /root/.claude/settings.json << 'EOF'
{
  "env": {
    "BASH_MAX_TIMEOUT_MS": "86400000",
    "BASH_DEFAULT_TIMEOUT_MS": "86400000"
  }
}
EOF

CMD ["bash"]