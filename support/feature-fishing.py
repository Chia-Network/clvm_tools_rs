#!/usr/bin/env python

from tomlkit import parse

cargo_toml = parse(open('Cargo.toml').read())
print(",".join(list(filter(lambda x: x != 'extension-module', cargo_toml['features']['default']))))
