Build
-----

Use `wasm-pack` to build the wasm `pkg` file used with npm. Install it with:

```bash
cargo install wasm-pack
```

Then build with

```bash
# Make sure you're at <clvm_tools_rs root>/wasm
wasm-pack build --release --target=web
```

Test
-----
Prerequisite:
- NodeJS >= 16
- Wasm files built by `wasm-pack` command exist at `<clvm_tools_rs root>/wasm/pkg/`

```bash
# Make sure you're at <clvm_tools_rs root>/wasm
node ./tests/index.js
```
