FROM ubuntu:24.04
 
WORKDIR /usr/src
COPY . .
RUN apt-get update && apt-get install -y \
    build-essential \
    git \
    wget \
    python3-pip \
    python3-venv

RUN chmod +x install.sh test.sh && ./install.sh
 
# ENTRYPOINT ["./test.sh"]
