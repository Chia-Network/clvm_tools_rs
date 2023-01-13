Build
-----

Clone GitHub repository
```bash
git clone https://github.com/Chia-Network/clvm_tools_rs
cd clvm_tools_rs/wasm
```

Use `wasm-pack` to build the wasm `pkg` file used with npm. Install it with:

```bash
cargo install wasm-pack
```

Then build with

```bash
# Make sure you're at <clvm_tools_rs root>/wasm
wasm-pack build --release --target=nodejs
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
