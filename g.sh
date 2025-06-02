#!/usr/bin/env sh

python generate_arithmetic.py
python proofcov/proofcov.py examples/arith/arith01.tests
