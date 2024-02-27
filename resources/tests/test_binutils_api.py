from clvm_tools_rs import binutils
from clvm_tools.binutils import assemble

expected = assemble("(q)")
assembled = binutils.assemble("(q)")

# assembled should return a clvm.SExp object, but currently just returns a string
assert expected == assembled
