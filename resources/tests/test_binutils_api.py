from clvm_tools_rs import binutils
from clvm_tools.binutils import assemble
from clvm_rs.program import Program

test_cases = [
    "(q)",
    "()",
    "(1 . 2)",
    "(() . ())",
    "(1 2 3 . ())",
    "(1 2 3)",
    "((4 5 6) (7 8 9))",
    "(i (q . 1) (q . 2) (q . 3))"
];

for t in test_cases:
    expected = assemble(t)
    assembled = binutils.assemble_generic(lambda x,y: Program.to((x,y)), Program.to, t)

    # assembled should return a clvm.SExp object, but currently just returns a string
    assert expected == assembled
