#!/usr/bin/env python3
"""Combine local implementation includes into one official-interface source."""
import argparse
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def expand(path, seen):
    path = path.resolve()
    if path in seen:
        raise ValueError('recursive local include: ' + path.name)
    seen = seen | {path}
    output = []
    for line in path.read_text().splitlines(keepends=True):
        match = re.fullmatch(r'\s*#\s*include\s+"([^"]+)"\s*\n?', line)
        if match and match.group(1) != 'solution.h':
            target = (path.parent / match.group(1)).resolve()
            if ROOT not in target.parents:
                raise ValueError('include escapes repository')
            output.append('// --- ' + str(target.relative_to(ROOT)) + ' ---\n')
            output.append(expand(target, seen))
        else:
            output.append(line)
    return ''.join(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'build/Solution.cpp')
    args = parser.parse_args()
    text = expand(ROOT / 'src/solution.cpp', set())
    assert text.startswith('#include "solution.h"')
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(text)
    print('Wrote', args.out)


if __name__ == '__main__':
    main()
