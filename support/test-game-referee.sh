#!/bin/bash -x

python -m pip install --upgrade pip
python -m pip install chia_rs==0.2.5
python -m pip install clvm_tools
python -m pip install pytest

export PYTHONPATH=$PWD/resources/tests:.:$PYTHONPATH
(cd resources/tests/game-referee-after-cl21 && pytest -s .)
