use std::env;
use std::error::Error;
use wapc::WapcHost;

use indoc::indoc;

// Steps:
//
// For program:
//
// Do conversions of subobjects, naming them by their hashes, writing out
// registered assemblyscript functions.
//
// Aux functions:
//
// - is_cons(addr) -> [] / [p1, p2]
// - atom_val(addr) -> [bytes...]
//
// - create_value(bytes) -> [ptr]
//
// Compile assemblyscript
//
// Load wasm
//
// Call toplevel program.
//
// Assemblyscript format:
//
// Heap contains only
//  - 0x00000000 <ptr1> <ptr2>
//  - 0x00000001 <len>  ...
//

//
// Host callbacks:
//
// clvm_op
//

const AS_FUNCTION_PREAMBLE: &str = indoc!{"
   var val_stack: Array<ArrayBuffer> = new Array<ArrayBuffer>();
"};

const AS_FUNCTION_END: &str = indoc!{"
    if (val_stack.length != 1) {
        return Result.error("wrong val stack length after function call");
    }
    return Result.ok(val_stack.pop());
"};

fn compose_clvm_function(name: &str, body: Rc<SExp>) -> Result<String, String> {
    
}

pub fn main() -> Result<(), Box<dyn Error>> {
    // Sample host callback that prints the operation a WASM module requested.
    let host_callback = |id: u64, bd: &str, ns: &str, op: &str, payload: &[u8]| {
        println!("Guest {} invoked '{}->{}:{}' with a {} byte payload",
                 id, bd, ns, op, payload.len());
        // Return success with zero-byte payload.
        Ok(vec![])
    };

    let args: Vec<String> = std::env::args().skip(1).take(1).collect();
    let module_bytes = std::fs::read(&args[0])?;
    let first_of_bytes: Vec<u8> = module_bytes.iter().take(4).copied().collect();
    eprintln!("module_bytes {first_of_bytes:?}");

    let builder = wasmtime_provider::WasmtimeEngineProviderBuilder::new()
        .module_bytes(&module_bytes);
    eprintln!("builder made");
    let engine = builder.build().expect("engine");
    eprintln!("have engine");
    let host = WapcHost::new(Box::new(engine), Some(Box::new(host_callback)))?;

    let res = host.call("hello", b"payload bytes")?;
    eprintln!("hello {res:?}");

    let nil_atom: &[u8; 4] = &[0,0,0,0];
    let created_atom = host.call("create_value", nil_atom);
    eprintln!("created_atom {created_atom:?}");

    let try_hash: &[u8; 32] = b"0123456_1234567_2345678_3456789_";
    let hash_res = host.call("test_hash_from_arraybuffer", try_hash);
    eprintln!("hash_res {hash_res:?}");

    let try_fun_res = host.call("test_run_function_by_address", &created_atom.expect("should have worked"));
    eprintln!("try_fun_res {try_fun_res:?}");

    Ok(())
}
