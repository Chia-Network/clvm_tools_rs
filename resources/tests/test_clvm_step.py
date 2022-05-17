#!/usr/bin/env python3
import os
from pathlib import Path
import json
from clvm_tools_rs import start_clvm_program

def simple_test():
    p = start_clvm_program('ff02ffff01ff02ff02ffff04ff02ffff04ff05ff80808080ffff04ffff01ff02ffff03ffff09ff05ffff010180ffff01ff0101ffff01ff12ff05ffff02ff02ffff04ff02ffff04ffff11ff05ffff010180ff808080808080ff0180ff018080', 'ff0580', {"de3687023fa0a095d65396f59415a859dd46fc84ed00504bf4c9724fca08c9de":"factorial"})

    last = None
    location = None
    while not p.is_ended():
        step_result = p.step()
        if step_result is not None:
            last = step_result
            if 'Operator-Location' in last:
                location = last['Operator-Location']
            print(json.dumps(step_result))

    assert int(last['Final']) == 120
    assert location.startswith('factorial')

def complex_test():
    mypath = Path(os.path.abspath(__file__))
    testpath = mypath.parent.joinpath('steprun')
    symbols = json.loads(open(str(testpath.joinpath('fact.sym'))).read())

    def fact_base_override(env):
        print('fact_base_override')
        return 99

    p = start_clvm_program(open(str(testpath.joinpath('fact.clvm.hex'))).read(), 'ff0580', symbols, {
        "fact-base": fact_base_override
    })

    last = None
    location = None
    while not p.is_ended():
        step_result = p.step()
        if step_result is not None:
            last = step_result
            if 'Operator-Location' in last:
                location = last['Operator-Location']
            print(json.dumps(step_result))

    assert int(last['Final']) == 11880

if __name__ == '__main__':
    simple_test()
    complex_test()
