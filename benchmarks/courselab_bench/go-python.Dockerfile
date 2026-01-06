FROM python:3.12.6

ARG DEBIAN_FRONTEND=noninteractive
ENV TZ=Etc/UTC

WORKDIR /
ADD . .

# SWE-ReX will always attempt to install its server into your docker container
# however, this takes a couple of seconds. If we already provide it in the image,
# this is much faster.
RUN pip install pipx
RUN pipx install swe-rex 
RUN pipx ensurepath

RUN pip install flake8

ENV GOLANG_VERSION=1.22.3

RUN apt-get update && apt-get install -y wget tar git build-essential \
    && wget https://go.dev/dl/go${GOLANG_VERSION}.linux-amd64.tar.gz \
    && tar -C /usr/local -xzf go${GOLANG_VERSION}.linux-amd64.tar.gz \
    && rm go${GOLANG_VERSION}.linux-amd64.tar.gz \
    && apt-get clean && rm -rf /var/lib/apt/lists/*

ENV PATH="/usr/local/go/bin:${PATH}"

SHELL ["/bin/bash", "-c"]
# This is where pipx installs things
ENV PATH="$PATH:/root/.local/bin/"

# Write PATH to profile files so it's available in login shells (bash -lc)
RUN echo 'export PATH="/usr/local/go/bin:/root/.local/bin:$PATH"' >> /etc/profile && \
    echo 'export PATH="/usr/local/go/bin:/root/.local/bin:$PATH"' >> /root/.bashrc

RUN python --version && go version

CMD ["bash"]
