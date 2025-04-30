import sys
import toml
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--change-pkg', default=None)
parser.add_argument('--target-path', default=None)
parser.add_argument('tomlfile')

args = parser.parse_args()

if args.change_pkg is None:
    print('specify a package to change with --change-pkg')
    sys.exit(1)

if args.target_path is None:
    print('specify a path with --target-path')
    sys.exit(1)

tfile = toml.load(args.tomlfile)
section = tfile['tool']['poetry']['dependencies']
section[args.change_pkg] = {"path": args.target_path}
with open(args.tomlfile, 'w') as f:
    toml.dump(tfile, f)

