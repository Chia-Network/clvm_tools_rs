#!/usr/bin/env python
from testbuild import compile_programs

programs = [
    ('gameref21/rockpaperscissorsd.clsp',['./gameref21']),
    ('gameref21/rockpaperscissorsc.clsp',['./gameref21']),
    ('gameref21/rockpaperscissorsb.clsp',['./gameref21']),
    ('gameref21/rockpaperscissorsa.clsp',['./gameref21']),
    ('gameref21/referee_accuse.clsp',['./gameref21']),
    ('gameref21/referee.clsp',['./gameref21']),
    ('bridgeref/merkle_tree_a2c.clsp',['./bridge-includes']),
    ('bridgeref/validation_taproot.clsp',['./bridge-includes'])
]

compile_programs(programs)
