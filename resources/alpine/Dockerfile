FROM alpine:latest
WORKDIR /root
RUN apk add git curl python3 openssl openssl-dev perl linux-headers make gcc musl-dev patch patchelf py3-pip
RUN curl --proto '=https' --tlsv1.2 -sSf -o rustup https://sh.rustup.rs
RUN sh ./rustup -y
WORKDIR /root/clvm_tools_rs
RUN python3 -m venv venv
RUN source venv/bin/activate
RUN pip install maturin[patchelf]
COPY ./build-alpine.sh /root
