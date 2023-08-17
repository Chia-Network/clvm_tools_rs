import binascii
import json
import os
from pathlib import Path
from typing import List

# from chia.types.blockchain_format.program import Program
from clvm_rs import Program
from clvm_tools.binutils import assemble, disassemble

from clvm_tools_rs import compile_clvm, compose_run_function, start_clvm_program


def compile_module_with_symbols(include_paths: List[Path], source: Path):
    path_obj = Path(source)
    file_path = path_obj.parent
    file_stem = path_obj.stem
    target_file = file_path / (file_stem + ".clvm.hex")
    sym_file = file_path / (file_stem + ".sym")
    # print(f"compile_clvm({path_obj.absolute()}, {str(target_file.absolute().as_posix())}, {include_paths}, True)")
    compile_result = compile_clvm(
        str(path_obj.resolve()), str(target_file.absolute()), [str(p) for p in include_paths], True
    )
    print(f"Writing to {target_file} {compile_result}")
    # symbols = compile_result["symbols"]
    # if len(symbols) != 0:
    #    with open(str(sym_file.absolute()), "w") as symfile:
    #        symfile.write(json.dumps(symbols))


def run_until_end(p):
    last = None
    location = None

    while not p.is_ended():
        step_result = p.step()
        if step_result is not None:
            last = step_result
            if "Print" in last:
                to_print = last["Print"]
                if "Print-Location" in last:
                    print(f"{last['Print-Location']}: print {to_print}")
                else:
                    print(f"print {to_print}")

    return last


def diag_run_clvm(program, args, symbols):
    hex_form_of_program = binascii.hexlify(bytes(program)).decode("utf8")
    hex_form_of_args = binascii.hexlify(bytes(args)).decode("utf8")
    symbols = json.loads(open(symbols).read())
    p = start_clvm_program(
        hex_form_of_program, hex_form_of_args, symbols, None
    )
    report = run_until_end(p)
    if "Failure" in report:
        raise Exception(report)
    else:
        return assemble(report["Final"])


if __name__ == "__main__":
    # smoke test
    import sys

    program = Program.fromhex(open(sys.argv[1]).read())
    args = Program.fromhex(open(sys.argv[2]).read())
    diag_run_clvm(program, args)
