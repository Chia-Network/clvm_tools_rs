#!/bin/bash -x 

if true; then
python -m pip install --upgrade pip
python -m pip install clvm_rs
python -m pip install clvm_tools
python -m pip install pytest
fi > /dev/null

export PYTHONPATH=$PWD/resources/tests:.:$PYTHONPATH
(cd resources/tests/game-referee-after-cl21 && pytest -s .)

