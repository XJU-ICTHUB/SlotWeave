#!/usr/bin/env python3
"""Independent score oracle and deterministic generated interface tests."""
import argparse
import collections
import json
import math
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def uniformity(layout):
    """Direct floating-point definition; independent of solver's integer model."""
    n = len(layout)
    positions = collections.defaultdict(list)
    for index, label in enumerate(layout):
        positions[label].append(index)
    total = 0.0
    for places in positions.values():
        s = len(places)
        if s <= 1 or s == n:
            value = 1.0
        else:
            gaps = [places[i + 1] - places[i] for i in range(s - 1)]
            gaps.append(places[0] + n - places[-1])
            deviation = sum(abs(gap - n / s) for gap in gaps)
            value = 1 - deviation / (2 * (s - 1) * (n / s - 1))
        total += s / n * value
    return total


def counts(layout):
    return {label: size for label, size in collections.Counter(layout).items() if size}


def read_case(path):
    words = iter(map(int, path.read_text().split()))
    n, m = next(words), next(words)
    services = [(next(words), next(words)) for _ in range(m)]
    q = next(words)
    ops = [(next(words), next(words), next(words)) for _ in range(q)]
    assert next(words, None) is None
    return n, services, ops


def check_trace(case, result):
    n, services, operations = case
    expected = collections.Counter()
    for label, count in services:
        expected[label] += count
    expected[0] = n - sum(expected.values())
    previous = result['initial']
    assert len(previous) == n and counts(previous) == {x: c for x, c in expected.items() if c}
    assert len(result['steps']) == len(operations)
    qualities = []
    for (op, label, request), step in zip(operations, result['steps']):
        k = 0 if label == 0 else min(max(request, 0), expected[0 if op == 1 else label])
        if label != 0:
            expected[label] += k if op == 1 else -k
            expected[0] -= k if op == 1 else -k
        current = step['grid']
        assert len(current) == n and counts(current) == {x: c for x, c in expected.items() if c}
        changed = sum(a != b for a, b in zip(previous, current))
        assert k <= changed <= n
        if k == 0:
            assert previous == current
        u = uniformity(current)
        v = 1.0 if k == n else 1 - (changed - k) / (n - k)
        assert step['K'] == k and step['M'] == changed
        assert math.isclose(step['U'], u, abs_tol=1e-11)
        assert math.isclose(step['V'], v, abs_tol=1e-11)
        qualities.append(0.55 * u + 0.35 * v)
        previous = current
    quality = sum(qualities) / len(qualities)
    assert math.isclose(result['summary']['quality'], quality, abs_tol=1e-11)
    return quality


def generate_case(rng, n, q, serial):
    # This seed belongs to published regression tests; it is not an algorithm input.
    services = []
    left = n
    for i in range(min(n, 6)):
        amount = rng.randint(0, left)
        if amount:
            services.append((1000000007 - 7919 * i, amount))
            left -= amount
    if serial % 5 == 0 and services:
        # Duplicate IDs and reordered initial services must remain legal.
        label, amount = services[0]
        if amount > 1:
            services[0] = (label, amount // 2)
            services.append((label, amount - amount // 2))
        rng.shuffle(services)
    expected = collections.Counter(dict(services))
    # Build the real histogram even for duplicate initial IDs.
    expected.clear()
    for label, count in services:
        expected[label] += count
    expected[0] = n - sum(expected.values())
    ids = [label for label, _ in services] + [17, -7, 2147483647, -2147483647, 0]
    operations = []
    for index in range(q):
        op = rng.choice((1, 2))
        label = rng.choice(ids)
        request = rng.choice((0, -1, 1, 2, max(1, n // 7), n, n + 3, rng.randint(1, n + 1)))
        operations.append((op, label, request))
    return n, services, operations


def write_case(path, case):
    n, services, operations = case
    rows = [f'{n} {len(services)}'] + [f'{x} {s}' for x, s in services]
    rows += [str(len(operations))] + [f'{op} {x} {c}' for op, x, c in operations]
    path.write_text('\n'.join(rows) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runner', type=Path, required=True)
    parser.add_argument('--reference', type=Path, help='optional same-configuration runner for exact trajectory comparison')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    runner = args.runner.resolve()
    assert math.isclose(uniformity([1, 0, 1, 1, 2, 2]), 5 / 12, abs_tol=1e-12)
    assert math.isclose(uniformity([1, 2, 0, 1, 2, 0]), 1, abs_tol=1e-12)
    assert uniformity([7]) == uniformity([7] * 6) == 1
    rng = random.Random(20261019)
    records = []
    with tempfile.TemporaryDirectory(prefix='timeslot-tests-') as directory:
        temp = Path(directory)
        cases = [(p.stem, read_case(p)) for p in sorted((ROOT / 'tests/data').glob('*.txt'))]
        for i in range(48):
            n = (1, 2, 3, 6, 7, 10, 17, 31, 64, 97, 257, 1000)[i % 12]
            cases.append((f'generated_{i:02}', generate_case(rng, n, 45, i)))
        cases += [
            ('max_full_noop', (10000, [(1, 10000)], [(1, 2, 1), (2, 2, 1)] * 500)),
            ('max_heavy', (10000, [(1, 4000), (2, 4000)], [(1, 1, 512), (2, 1, 512)] * 30)),
            ('max_light', (10000, [(1, 4000), (2, 4000)], [(1, 1, 1), (2, 1, 1)] * 500)),
            ('max_replace', (10000, [(1, 10000)], [(2, 1, 10000), (1, 2, 10000)])),
            ('many_types', (2000, [(i + 1, 10) for i in range(100)],
                            [(1, 10001 + i, 1) for i in range(250)] + [(2, i + 1, 10) for i in range(100)])),
        ]
        for index, (name, case) in enumerate(cases):
            path = temp / f'{index:03}.txt'
            write_case(path, case)
            call = [str(runner), str(path), '--trace']
            completed = subprocess.run(call, check=True, text=True, capture_output=True, timeout=60)
            assert not completed.stderr.strip(), (name, completed.stderr)
            result = json.loads(completed.stdout)
            quality = check_trace(case, result)
            if args.reference:
                reference_run = subprocess.run([str(args.reference.resolve()), str(path), '--trace'],
                    check=True, text=True, capture_output=True, timeout=60)
                assert not reference_run.stderr.strip(), (name, reference_run.stderr)
                reference = json.loads(reference_run.stdout)
                assert reference['initial'] == result['initial'] and reference['steps'] == result['steps'], name
            if index < 3:
                again_run = subprocess.run(call, check=True, text=True, capture_output=True, timeout=60)
                assert not again_run.stderr.strip(), (name, again_run.stderr)
                again = json.loads(again_run.stdout)
                assert result['initial'] == again['initial'] and result['steps'] == again['steps']
            records.append({'name': name, 'N': case[0], 'Q': len(case[2]), 'quality': quality,
                            'operation_us': result['summary']['operation_us'],
                            'extra_changed_total': result['summary']['extra_changed_total']})
    report = {'status': 'PASS', 'cases': len(records), 'operations': sum(r['Q'] for r in records),
              'seed': 20261019, 'score_scope': 'local quality only; official speed references unavailable',
              'checks': ['independent count/score oracle', 'no-op identity', 'init reset', 'grid repeat',
                         'determinism', 'clamps', 'sparse IDs', 'new types', 'N=K', 'max N/Q workloads'],
              'rows': records}
    if args.reference:
        report['exact_reference_trajectory_cases'] = len(records)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f"PASS: {report['cases']} cases, {report['operations']} operations; independent scores and interface properties")


if __name__ == '__main__':
    main()
