#!/bin/sh

#version details
VERSION=16.15.0
PLATFORM=linux
ARCH=x86
PREFIX="$HOME/node-v$VERSION-$PLATFORM-$ARCH"

#download binaries
mkdir -p "$PREFIX" && \
curl https://nodejs.org/dist/v$VERSION/node-v$VERSION-linux-x64.tar.xz \
  | xz -d | tar xvf - --strip-components=1 -C "$PREFIX"

${PREFIX}/bin/node "${@}"
