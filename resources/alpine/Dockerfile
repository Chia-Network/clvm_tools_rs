FROM alpine:3.16.2
WORKDIR /root
RUN sh -c "echo https://mirrors.edge.kernel.org/alpine/v3.16.2/community >> /etc/apk/repositories"
RUN apk add git curl python3 openssl openssl-dev perl linux-headers make gcc musl-dev patch patchelf
RUN curl --proto '=https' --tlsv1.2 -sSf -o rustup https://sh.rustup.rs
RUN sh ./rustup -y
COPY build-openssl.sh .
RUN sh ./build-openssl.sh
RUN curl https://files.pythonhosted.org/packages/b1/77/75f6543eafdffc0b3f07f99682497bea817ef0b6c361fe72b932eb82459c/setuptools-62.2.0.tar.gz | tar xzvf -
COPY wheel.diff setuptools-62.2.0
RUN cd setuptools-62.2.0 && patch -p1 < wheel.diff
RUN curl https://files.pythonhosted.org/packages/99/bb/696e256f4f445809f25efd4e4ce42ff99664dc089cafa1e097d5fec7fc33/pip-22.1.tar.gz | tar xzvf -
RUN sh -c "cd setuptools-62.2.0 && python3 setup.py install"
RUN curl https://files.pythonhosted.org/packages/99/bb/696e256f4f445809f25efd4e4ce42ff99664dc089cafa1e097d5fec7fc33/pip-22.1.tar.gz | tar xzvf -
RUN sh -c "cd pip-22.1 && python3 setup.py install"
RUN pip install maturin
WORKDIR /root/clvm_tools_rs
COPY ./build-alpine.sh /root