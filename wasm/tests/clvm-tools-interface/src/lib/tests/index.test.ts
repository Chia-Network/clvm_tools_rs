import * as fs from 'fs';
import { resolve } from 'path';
import * as assert from 'assert';
import * as bls_loader from 'bls-signatures';
const {h, t, Program, compile, get_dependencies} = require('../../../../../pkg/clvm_tools_wasm');

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
        assert.fail(true);
    } catch (e) {
        assert.equal(e.toString(), "not a number");
    }
});

it('Has as_bigint', async () => {
    let int_value = Program.to(10000000000000000000000n).as_bigint();
    assert.equal(int_value, 10000000000000000000000n);
    try {
        non_int_value = Program.to([7,13]).as_bigint();
        assert.fail(true);
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
        assert.fail(true);
    } catch (e) {
        assert.equal(e.toString(), "not a cons");
    }
    try {
        Program.to([]).rest();
        assert.fail(true);
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

it('Has the t function', async () => {
    let p1 = Program.to(7);
    let p2 = Program.to(9);
    let tuple = t(p1, p2);
    let consed = p1.cons(p2);
    assert.equal(Program.to(tuple).toString(), consed.toString());
});

it('Has as_bin', async () => {
    let test_data = Program.to([7,8,9,10]);
    let as_bin = test_data.as_bin();
    assert.equal([255,7,255,8,255,9,255,10,128].toString(), as_bin.toString());
});

it('Has list_len', async () => {
    let list_data = Program.to([7,8,9,10]);
    let list_len = list_data.list_len();
    assert.equal(list_len, 4);
    let not_list = Program.to(16);
    let not_list_len = not_list.list_len();
    assert.equal(not_list_len, 0);
});

it('Has equal_to', async () => {
    let p1 = Program.to([7,8,[9,10],11]);
    let p2 = Program.from_hex('ff07ff08ffff09ff0a80ff0b80');
    let p3 = Program.to([7,8,[9,11],11]);
    assert.ok(p1.equal_to(p2));
    assert.ok(!p1.equal_to(p3));
    assert.ok(!p2.equal_to(p3));
});

it('Has as_javascript', async () => {
    let tuple = t(9,(t(10,11)));
    let original = [7,8,tuple,12];
    let p1 = Program.to(original);
    let p1_as_js = p1.as_javascript();
    assert.equal(original.toString(), p1_as_js.toString());
});

it('Has run', async () => {
    let program = Program.from_hex('ff12ffff10ff02ffff010180ffff11ff02ffff01018080');
    let args = Program.to([13]);
    const [cost, run_result] = program.run(args);
    assert.equal(run_result.toString(), '8200a8');
    assert.equal(cost, 2658);
});

it('Has run with operator override', async () => {
    let program = Program.from_hex('ff907370656369616c2d6f70657261746f72ff02ff0580');
    let n1 = 101;
    let n2 = 523;
    let args0 = Program.to([n1,n2]);
    let options = {
        "operators": {
            "special-operator": (args) => {
                let first_arg = args.first().as_int();
                let second_arg = args.rest().first().as_int();
                return Program.to(first_arg ^ second_arg);
            }
        }
    };
    const [cost0, run_result0] = program.run(args0, options);
    assert.equal(run_result0.as_int(), 622);

    let args1 = Program.to([]);
    try {
        program.run(args1, options);
        assert.fail(true);
    } catch (e) {
        assert.equal(e.toString(), Program.to(t([], "path into atom")).toString());
    }
});

it('Can run isolated code and examine the result', async () => {
    let program = Program.from_hex('ff02ffff01ff02ff02ffff04ff02ffff04ff05ffff04ff0bff8080808080ffff04ffff01ff9272756e2d776974682d657863657074696f6eff05ff0b80ff018080');
    let use_program = Program.from_hex('ff02ffff01ff02ffff03ff05ffff01ff02ffff01ff02ff02ffff04ff02ff058080ff0180ffff01ff02ffff01ff08ffff018d6e6f206172677320676976656e80ff018080ff0180ffff04ffff01ff02ffff0117ff0180ff018080');
    let options = {
        "operators": {
            "run-with-exception": (args) => {
                let program = args.first();
                let env = args.rest().first();
                try {
                    let [cost, result] = program.run(env);
                    return Program.to(t(result, []));
                } catch (e) {
                    return Program.to(t([], e));
                }
            }
        }
    };

    let args0 = Program.to([use_program, [[1, 2, 3]]]);
    const [cost0, run_result0] = program.run(args0, options);
    assert.equal(run_result0.first().as_int(), 3);
    assert.ok(run_result0.rest().nullp());

    let args1 = Program.to([use_program, [[1, 2]]]);
    const [cost1, run_result1] = program.run(args1, options);
    assert.ok(run_result1.first().nullp());
    assert.equal(
        run_result1.rest().toString(),
        Program.to(t([], "path into atom")).toString()
    );

    let args2 = Program.to([use_program, [[]]]);
    const [cost2, run_result2] = program.run(args2, options);
    assert.ok(run_result2.first().nullp());
    assert.equal(
        run_result2.rest().first().toString(),
        Program.to("no args given").toString()
    );
    assert.equal(
        run_result2.rest().rest().toString(),
        Program.to("clvm raise").toString()
    );
});

it('Has curry', async () => {
    let program = Program.from_hex('ff12ffff10ff02ffff010180ffff11ff02ffff01018080');
    let program_with_arg = program.curry(Program.to(13));
    const [cost, run_result] = program_with_arg.run(Program.to([]));
    assert.equal(run_result.toString(), '8200a8');
    assert.equal(cost, 2884);
});

export class ChiaExample {
    constructor(MOD) {
        this.MOD = MOD;
    }
    public puzzle_for_synthetic_public_key(synthetic_public_key: G1Element): Program {
        return this.MOD.curry(synthetic_public_key);
    }
}

it('works as expected in context', async () => {
    let bls = await bls_loader.default();
    const program_text = fs.readFileSync(resolve(__dirname, '../../../content/p2_delegated_puzzle_or_hidden_puzzle.clvm.hex'),'utf-8');
    const MOD: Program = Program.from_hex(program_text);
    let ce = new ChiaExample(MOD);
    let sk = bls.AugSchemeMPL.key_gen([
        0, 50, 6, 244, 24, 199, 1, 25, 52, 88, 192, 19, 18, 12, 89, 6, 220,
        18, 102, 58, 209, 82, 12, 62, 89, 110, 182, 9, 44, 20, 254, 22
    ]);
    let pk = bls.AugSchemeMPL.sk_to_g1(sk);
    // pk bytes 86243290bbcbfd9ae75bdece7981965350208eb5e99b04d5cd24e955ada961f8c0a162dee740be7bdc6c3c0613ba2eb1
    // Expected puzzle hash = 30cdae3d54778db5eba21584c452cfb1a278136b2ec352ba44a52078efea7507
    let target_puzzle = ce.puzzle_for_synthetic_public_key(pk);
    assert.equal(target_puzzle.sha256tree().toString(), h('30cdae3d54778db5eba21584c452cfb1a278136b2ec352ba44a52078efea7507').toString());
});

function compiler_read_file(filename, dirs) {
    for (let d in dirs) {
        let dir = dirs[d];
        let path = resolve(dir, filename);
        try {
            return [path, fs.readFileSync(path, 'utf8')];
        } catch (e) {
            // Ok, try the next dir.
        }
    }

    throw `Could not find file ${filename}`;
}

it('can compile complex programs', async () => {
    let filename = resolve(__dirname, '../../../content/test-with-include.clsp');
    let program_text = fs.readFileSync(filename, 'utf8');
    let program_output = compile(
        program_text,
        filename,
        [resolve(__dirname, '../../../content')],
        { 'read_new_file': compiler_read_file }
    );
    assert.equal(program_output.hex, 'ff10ff02ffff010380');
});

it('can get dependencies', async () => {
    let filename = resolve(__dirname, '../../../content/test-with-include.clsp');
    let program_text = fs.readFileSync(filename, 'utf8');
    let deplist = get_dependencies(
        program_text,
        filename,
        [resolve(__dirname, '../../../content')],
        { 'read_new_file': compiler_read_file }
    );
    assert.equal(deplist.length, 1);
    assert.equal(deplist[0], resolve(__dirname, '../../../content/test-include.clinc'));
});
