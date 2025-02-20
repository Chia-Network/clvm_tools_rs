#!/bin/sh

. $HOME/.cargo/env
cd /root/clvm_tools_rs
python3 -m venv venv
source ./venv/bin/activate
pip install maturin[patchelf]
CC=gcc maturin build --release --strip --compatibility musllinux_1_1 --target x86_64-unknown-linux-musl
