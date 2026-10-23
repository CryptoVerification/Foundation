"""Exact algebra for repair of noisy labeled classical one-bit ciphers.

Finite checks supplement the proofs in polygraphic-novelty-audit.md. They
do not prove a homotopy obstruction or certify Foundation machine execution.
"""
from fractions import Fraction as F
from pathlib import Path
from random import Random
import hashlib
import importlib.util
import json

DEPENDENCY = Path(__file__).with_name('classical-bit-encryption-control.py')
spec = importlib.util.spec_from_file_location('frozen_control', DEPENDENCY)
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


def l1(vector):
    return sum(abs(x) for x in vector)


def joint(cipher, message):
    weights, enc, _ = cipher
    return [p * value for p, row in zip(weights, enc)
            for value in (row[message], 1-row[message])]


def metrics(cipher):
    weights, enc, dec = cipher
    assert sum(weights) == 1 and min(weights) >= 0
    assert all(0 <= x <= 1 for row in enc+dec for x in row)
    epsilon = abs(sum(p*(a-b) for p, (a, b) in zip(weights, enc)))
    errors = [F(0), F(0)]
    for p, (a, b), (u, v) in zip(weights, enc, dec):
        if not p:
            continue
        recovered0 = a*u+(1-a)*v
        recovered1 = b*u+(1-b)*v
        error0, error1 = 1-recovered0, recovered1
        assert abs(a-b) >= 1-error0-error1
        errors[0] += p*error0
        errors[1] += p*error1
    return epsilon, max(errors)


def repair(cipher):
    weights, enc, _ = cipher
    epsilon, delta = metrics(cipher)
    assert epsilon+2*delta < 1
    signed = [p*(a-b) for p, (a, b) in zip(weights, enc)]
    length, bias = l1(signed), sum(signed)
    assert length >= 1-2*delta and abs(bias) == epsilon
    positive = sum(x for x in signed if x > 0)
    negative = -sum(x for x in signed if x < 0)
    assert 2*min(positive, negative) >= 1-2*delta-epsilon > 0
    out = [x/(2*positive) if x > 0 else x/(2*negative) for x in signed]
    c.cipher_check(out)
    return out, signed


def perfect(vector):
    rows = [(F(1), F(0)) if x >= 0 else (F(0), F(1)) for x in vector]
    return list(map(abs, vector)), rows, rows


def noisy(vector, rng):
    enc, dec = [], []
    for value in vector:
        a, b = F(rng.randrange(9), 64), F(rng.randrange(9), 64)
        u, v = F(rng.randrange(5), 64), F(rng.randrange(5), 64)
        if value >= 0:
            enc.append((1-a, b))
            dec.append((1-u, v))
        else:
            enc.append((a, 1-b))
            dec.append((u, 1-v))
    return list(map(abs, vector)), enc, dec


def private_noisy_fill(point):
    radius = l1(point)
    assert sum(point) == 0 and radius <= 1
    weights = [abs(x)+(1-radius)/4 for x in point]
    rows = [((1+x/p)/2, (1-x/p)/2) if p else (F(1, 2), F(1, 2))
            for x, p in zip(point, weights)]
    # Each symmetric branch is its own chosen noisy decoder.
    return weights, rows, rows


def checks():
    rng = Random(2026102301)
    pool = []
    fixed = count = 0
    for keys in range(2, 9):
        for _ in range(64):
            raw = [F(rng.randrange(-16, 17)) for _ in range(keys)]
            mean = sum(raw)/keys
            if all(x == mean for x in raw):
                raw[0] += 1
                mean = sum(raw)/keys
            vector = c.normalize([x-mean for x in raw])
            assert repair(perfect(vector))[0] == vector
            fixed += 1
            cipher = noisy(vector, rng)
            epsilon, delta = metrics(cipher)
            repaired, signed = repair(cipher)
            pool.append((keys, cipher, repaired, signed, 1-epsilon-2*delta))
            count += 1
    pairs = 0
    for keys in range(2, 9):
        group = [entry for entry in pool if entry[0] == keys]
        for _ in range(128):
            _, a, ra, wa, ma = rng.choice(group)
            _, b, rb, wb, mb = rng.choice(group)
            distances = [l1([x-y for x, y in zip(joint(a, m), joint(b, m))])/2
                         for m in (0, 1)]
            metric = max(distances)
            assert l1([x-y for x, y in zip(wa, wb)]) <= sum(distances)
            margin = min(ma, mb)
            assert l1([x-y for x, y in zip(ra, rb)])/2 <= 2*metric/margin
            pairs += 1
    fill_count = boundary = 0
    for signs in ((1, 1, 1, -3), (1, -1, 0, 0), (-3, 1, 1, 1)):
        direction = c.normalize(list(map(F, signs)))
        for step in range(33):
            point = [F(step, 32)*x for x in direction]
            cipher = private_noisy_fill(point)
            epsilon, delta = metrics(cipher)
            assert epsilon == 0 and delta <= F(1, 2)
            if step == 0:
                assert delta == F(1, 2)
            if step == 32:
                assert delta == 0 and repair(cipher)[0] == direction
                boundary += 1
            fill_count += 1
    equality = 0
    for numerator in range(33):
        contrast = F(numerator, 32)
        cipher = ([F(1)], [((1+contrast)/2, (1-contrast)/2)], [(F(1), F(0))])
        epsilon, delta = metrics(cipher)
        assert epsilon+2*delta == 1
        equality += 1
    # The repair also handles ordinary correctness averaged over the key.
    # It can remove an uninformative positive-probability branch entirely.
    small = F(1, 1024)
    bad_branch = ([small, (1-small)/2, (1-small)/2],
                  [(F(1, 2), F(1, 2)), (F(1), F(0)), (F(0), F(1))],
                  [(F(1, 2), F(1, 2)), (F(1), F(0)), (F(0), F(1))])
    assert metrics(bad_branch) == (0, small/2)
    assert repair(bad_branch)[0] == [0, F(1, 2), -F(1, 2)]
    return {'perfect_ciphers_fixed_by_repair': fixed,
            'noisy_ciphers_repaired': count,
            'pairs_checking_repair_distance_bound': pairs,
            'noisy_four_key_fill_settings': fill_count,
            'exact_boundary_fill_settings': boundary,
            'sharp_threshold_equality_settings': equality,
            'rare_bad_key_probability': str(small),
            'rare_bad_key_average_error': str(small/2),
            'rare_bad_key_maximum_conditional_error': '1/2'}


def main():
    record = {'exact_rational_checks': checks(),
              'repair_condition': 'privacy_TV + 2*maximum_per_message_key_averaged_recovery_error < 1',
              'repair_distance_bound': 'repaired_joint_TV <= 2*original_joint_TV/margin',
              'finite_four_key_edge_lower_bound': 'margin/3, with exact nonnull boundary',
              'continuous_four_key_fill_at_recovery_error_one_half': True,
              'topological_nonextension_computer_verified': False,
              'ordinary_key_averaged_recovery_error_supported_algebraically': True,
              'Foundation_machine_realization_certified': False,
              'Lean_checked': False, 'newness_established': False,
              'source_sha256': {str(path.resolve()): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (Path(__file__), DEPENDENCY)}}
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
