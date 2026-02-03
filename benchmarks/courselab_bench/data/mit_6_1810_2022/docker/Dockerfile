FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    gcc-riscv64-linux-gnu \
    qemu-system-misc \
    python3 \
    git \
    ca-certificates \
    ipxe-qemu \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /root/workspace

CMD ["/bin/bash"]
