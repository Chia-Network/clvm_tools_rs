import MyLibrary from '../index';
import * as bls_loader from 'bls-signatures';
var clvm_tools_rs = require('../../../../../pkg/clvm_tools_wasm');

it('Runs without crashing', () => {
  new MyLibrary();
});

it('Has BLS signatures support', async () => {
    let bls = await bls_loader.default();
    let g1element = new bls.G1Element();
    console.log(g1element.__proto__);
    console.log(bls.G1Element);
    console.log(bls.G1Element.SIZE);
    console.log(g1element instanceof bls.G1Element);
    let g2element = new bls.G2Element();
    console.log(g2element.__proto__);
    console.log(bls.G2Element.SIZE);
    let converted_g1_element = clvm_tools_rs.sexp_to_string(g1element);
    let p = clvm_tools_rs.Program.to(13);
    console.log(p.toString());
    console.log(converted_g1_element);
});
