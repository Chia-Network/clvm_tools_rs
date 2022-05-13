#!/bin/sh

. $HOME/.cargo/env
CC=gcc maturin build --release --strip --compatibility musllinux_1_1 --target x86_64-unknown-linux-musl
