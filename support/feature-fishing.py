#!/usr/bin/env python

from tomlkit import parse
import sys

cargo_toml = parse(open('Cargo.toml').read())
results=",".join(list(filter(lambda x: x != 'extension-module', cargo_toml['features']['default'])))
if len(sys.argv) > 1:
    print(f"{sys.argv[1]}{results}")
else:
    print(results)
