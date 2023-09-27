#!/bin/bash -x

<<<<<<< HEAD
=======
if [ "x$1" = x ] ; then
    echo "usage: test-game-referee.sh [game-referee-version]"
    exit 1
fi

REF_SUBDIR="$1"

>>>>>>> chia/base
python -m pip install --upgrade pip
python -m pip install chia_rs==0.2.5
python -m pip install clvm_tools
python -m pip install pytest

export PYTHONPATH=$PWD/resources/tests:.:$PYTHONPATH
<<<<<<< HEAD
(cd resources/tests/game-referee-after-cl21 && pytest -s .)
=======
(cd "${REF_SUBDIR}" && pytest -s .)
>>>>>>> chia/base
