.PHONY: runmock.js

all: runmock.js

runmock.js:
	cd .. && cargo build --target wasm32-unknown-unknown && wasm-bindgen --nodejs --out-dir ./mock-test/build ./target/wasm32-unknown-unknown/debug/clvm_tools_rs.wasm
	./node_modules/.bin/webpack

run: runmock.js
	node ./build/runmock.js
