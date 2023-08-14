import MyLibrary from '../index';
import * as bls_loader from 'bls-signatures';
var clvm_tools_rs = require('../../../../../pkg/clvm_tools_wasm');

it('Runs without crashing', () => {
  new MyLibrary();
});

it('Has BLS signatures support', async () => {
    let bls = await bls_loader.default();
    let g1element = new bls.G1Element();
    let converted_g1_element = clvm_tools_rs.Program.to(g1element);
    console.log(converted_g1_element.toString());
});
