import * as assert from 'assert';
import * as bls_loader from 'bls-signatures';
const {h, Program} = require('../../../../../pkg/clvm_tools_wasm');

it('Has BLS signatures support', async () => {
    let bls = await bls_loader.default();
    let g1element = new bls.G1Element();
    let converted_g1_element = Program.to(g1element);
    assert.equal('b0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000', converted_g1_element.toString());
});

it('Has the "h" function', async () => {
    let unhexed = h('21203031');
    assert.equal([0x21, 0x20, 0x30, 0x31].toString(), unhexed.toString());
});

it('Converts to string', async () => {
    let converted_sexp = Program.to([1, 2, 3]);
    assert.equal("ff01ff02ff0380", converted_sexp.toString());
});

it('Accepts already converted objects', async () => {
    let converted_sexp = Program.to([1, 2, 3]);
    let twice_converted = Program.to(converted_sexp);
    assert.equal("ff01ff02ff0380", twice_converted.toString());
});

it('Has as_pair', async () => {
    let converted_sexp = Program.to([1, 2, 3]);
    let as_pair = converted_sexp.as_pair();
    assert.equal("01", as_pair[0].toString());
    assert.equal("ff02ff0380", as_pair[1].toString());
});

it('Has null', async () => {
    assert.equal(Program.null().toString(), '80');
});

it('Has listp', async () => {
    let is_list = Program.to([1,2,3]);
    let isnt_list = Program.to(456);
    assert.equal(is_list.listp(), true);
    assert.equal(isnt_list.listp(), false);
});

it('Has nullp', async () => {
    let is_null = Program.to([]);
    let is_also_null = Program.to(0);
    let isnt_null = Program.to(7);
    let isnt_also_null = Program.to([99,101]);
    assert.equal(is_null.nullp(), true);
    assert.equal(is_also_null.nullp(), true);
    assert.equal(isnt_null.nullp(), false);
    assert.equal(isnt_also_null.nullp(), false);
});

it('Has as_int', async () => {
    let int_value = Program.to(7).as_int();
    assert.equal(int_value, 7);
    try {
        non_int_value = Program.to([7,13]).as_int();
        assert.that(false);
    } catch (e) {
        assert.equal(e.toString(), "not a number");
    }
});

it('Has as_bigint', async () => {
    let int_value = Program.to(10000000000000000000000n).as_bigint();
    assert.equal(int_value, 10000000000000000000000n);
    try {
        non_int_value = Program.to([7,13]).as_bigint();
        assert.that(false);
    } catch (e) {
        assert.equal(e.toString(), "not a number");
    }
});

it('Has first and rest', async () => {
    let test_list = Program.to([7,13,17,23]);
    assert.equal(test_list.first().toString(), '07');
    assert.equal(test_list.rest().toString(), 'ff0dff11ff1780');
    try {
        Program.to([]).first();
        assert.that(false);
    } catch (e) {
        assert.equal(e.toString(), "not a cons");
    }
    try {
        Program.to([]).rest();
        assert.that(false);
    } catch (e) {
        assert.equal(e.toString(), "not a cons");
    }
});

it('Has cons', async () => {
    let test_1 = Program.to(7);
    let test_2 = Program.to([8,9,10]);
    let consed = test_1.cons(test_2);
    let test_3 = Program.to([7,8,9,10]);
    assert.equal(consed.toString(), test_3.toString());
});
