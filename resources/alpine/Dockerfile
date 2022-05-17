from alpine:3.15.4
workdir /root
run sh -c "echo https://mirrors.edge.kernel.org/alpine/v3.15.4/community >> /etc/apk/repositories"
run apk add git curl python3 openssl openssl-dev perl linux-headers make gcc musl-dev patch patchelf
run curl --proto '=https' --tlsv1.2 -sSf -o rustup https://sh.rustup.rs
run sh ./rustup -y
copy build-openssl.sh .
run sh ./build-openssl.sh
run curl https://files.pythonhosted.org/packages/b1/77/75f6543eafdffc0b3f07f99682497bea817ef0b6c361fe72b932eb82459c/setuptools-62.2.0.tar.gz | tar xzvf -
copy wheel.diff setuptools-62.2.0
run cd setuptools-62.2.0 && patch -p1 < wheel.diff
run curl https://files.pythonhosted.org/packages/99/bb/696e256f4f445809f25efd4e4ce42ff99664dc089cafa1e097d5fec7fc33/pip-22.1.tar.gz | tar xzvf -
run sh -c "cd setuptools-62.2.0 && python3 setup.py install"
run curl https://files.pythonhosted.org/packages/99/bb/696e256f4f445809f25efd4e4ce42ff99664dc089cafa1e097d5fec7fc33/pip-22.1.tar.gz | tar xzvf -
run sh -c "cd pip-22.1 && python3 setup.py install"
run pip install maturin
workdir /root/clvm_tools_rs
copy ./build-alpine.sh /root
