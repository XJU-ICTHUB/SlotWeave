#!/usr/bin/env python3
"""Audit the solver's own arithmetic, including every implementation fragment."""
import re
from pathlib import Path
from amalgamate import ROOT, expand


def code_only(source):
    return re.sub(r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'', ' ', source)


def main():
    text = expand(ROOT / 'src/solution.cpp', set())
    assert text.startswith('#include "solution.h"')
    code = code_only(text)
    banned = ['float', 'double', 'sqrt', 'pow', 'rand', 'srand', 'random_device', 'mt19937',
              'mt19937_64', 'printf', 'fprintf', 'cout', 'cin', 'fopen', 'chrono', 'main']
    for operator in ('*', '/', '%'):
        assert operator not in code, 'forbidden operator or star syntax: ' + operator
    for word in banned:
        assert not re.search(r'\b' + word + r'\b', code), 'forbidden identifier: ' + word
    assert not re.search(r'(?<![\w.])(\d+\.\d*|\.\d+|\d+[eE][+-]?\d+)', code)
    assert 'namespace smp_' not in code and 'namespace fit_' not in code
    print('PASS: all solver fragments use permitted own arithmetic; no I/O or sample/seed-fit wrapper')


if __name__ == '__main__':
    main()
