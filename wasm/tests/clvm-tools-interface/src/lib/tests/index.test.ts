import MyLibrary from '../index';
import * as bls_loader from 'bls-signatures';

it('Runs without crashing', () => {
  new MyLibrary();
});

it('Has BLS signatures support', async () => {
    let bls = await bls_loader.default();
    let g1element = new bls.G1Element();
    console.log(g1element.serialize());
});
