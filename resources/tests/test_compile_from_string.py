import clvm_tools_rs
import binascii

classic_code = """
(mod (N X)
  (defun F (N X) (if N (sha256 (F (- N 1) X)) X))
  (F N X)
  )
"""
expected_classic = binascii.unhexlify("ff02ffff01ff02ff02ffff04ff02ffff04ff05ffff04ff0bff8080808080ffff04ffff01ff02ffff03ff05ffff01ff0bffff02ff02ffff04ff02ffff04ffff11ff05ffff010180ffff04ff0bff808080808080ffff010b80ff0180ff018080".encode("utf8"))

cl23_code = """
(mod (N X)
  (include *standard-cl-23*)
  (defun F (N X) (if N (sha256 (F (- N 1) X)) X))
  (F N X)
  )
"""
expected_cl23 = binascii.unhexlify("ff02ffff01ff02ff02ffff04ff02ffff04ff05ffff04ff0bff8080808080ffff04ffff01ff02ffff03ff05ffff01ff0bffff02ff02ffff04ff02ffff04ffff11ff05ffff010180ffff04ff0bff808080808080ffff010b80ff0180ff018080".encode("utf8"))

compiled_code = clvm_tools_rs.compile(
    classic_code,
    ["."],
    True
)
# Classic outputs symbols to the filesystem down all routes, which likely should
# be fixed.
assert bytes(compiled_code["output"]) == expected_classic

compiled_code = clvm_tools_rs.compile(
    classic_code,
    ["."]
)
assert bytes(compiled_code) == expected_classic

compiled_code = clvm_tools_rs.compile(
    cl23_code,
    ["."],
    True
)
symbols = compiled_code["symbols"]
assert symbols["__chia__main_arguments"] == "(N X)"
assert symbols["30960d7f2ddc7188a6428a11d39a13ff70d308e6cc571ffb6ed5ec8dbe4376c0_arguments"] == "(N X)"
assert symbols["30960d7f2ddc7188a6428a11d39a13ff70d308e6cc571ffb6ed5ec8dbe4376c0"] == "F"
assert bytes(compiled_code["output"]) == expected_cl23
