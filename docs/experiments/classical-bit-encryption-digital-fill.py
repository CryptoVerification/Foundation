"""Exact rational five-key fill and bounded-coin quantization of a bit cipher.

This is a high-level algorithm, not a Foundation machine realization. The
digital four-key nonextension bound is proved mathematically in the audit.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from random import Random
import hashlib
import importlib.util
import json

DEPENDENCY = Path(__file__).with_name('classical-bit-encryption-control.py')
spec = importlib.util.spec_from_file_location('frozen_classical_control', DEPENDENCY)
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


def l1(vector):
    return sum(abs(x) for x in vector)


def fill(point):
    assert len(point) == 4 and sum(point) == 0
    radius = l1(point)
    assert radius <= 1
    center = [F(1, 8)]*4+[-F(1, 2)]
    raw = [x+(1-radius)*u for x, u in zip(point+[F(0)], center)]
    assert l1(raw) >= F(1, 3)
    return c.normalize(raw)


def quantize(vector, bits):
    c.cipher_check(vector)
    total = 2**bits
    counts = [0]*len(vector)
    for sign in (-1, 1):
        group = [i for i, value in enumerate(vector) if sign*value > 0]
        targets = {i: abs(vector[i])*total for i in group}
        for i in group:
            counts[i] = targets[i].numerator//targets[i].denominator
        left = total//2-sum(counts[i] for i in group)
        assert 0 <= left < len(group)
        ordered = sorted(group, key=lambda i: (targets[i]-counts[i], -i), reverse=True)
        for i in ordered[:left]:
            counts[i] += 1
        assert sum(counts[i] for i in group) == total//2
    out = [F(count, total)*(1 if value > 0 else -1) if count else F(0)
           for count, value in zip(counts, vector)]
    c.cipher_check(out)
    assert l1([x-y for x, y in zip(out, vector)]) <= F(len(vector), total)
    return out, counts


def distance(a, b):
    return l1([x-y for x, y in zip(a, b)])/2


def checks():
    directions = []
    for first in product(range(-1, 2), repeat=3):
        if any(first):
            directions.append(c.normalize([F(x) for x in first]+[-F(sum(first))]))
    points = [[F(step, 16)*x for x in direction] for direction in directions for step in range(17)]
    points += c.digital_tetrahedron(3)
    quantized = boundary_exact = 0
    for point in points:
        vector = fill(point)
        c.cipher_check(vector)
        if l1(point) == 1:
            assert vector == point+[F(0)]
        if l1(point) == 0:
            assert vector == [F(1, 8)]*4+[-F(1, 2)]
        for bits in (3, 4, 8, 12):
            out, counts = quantize(vector, bits)
            if all((x*2**bits).denominator == 1 for x in vector):
                assert out == vector
                if l1(point) == 1:
                    boundary_exact += 1
            assert sum(counts) == 2**bits
            quantized += 1
    rng = Random(87513)
    h, bits = F(1, 128), 8
    bound = 6*h+F(5, 2**bits)
    assert bound == F(17, 256) and bound < F(2, 3)
    worst = F(0)
    for _ in range(1024):
        x, z = rng.choice(points), rng.choice(points)
        y = [(1-h/2)*a+(h/2)*b for a, b in zip(x, z)]
        assert l1([a-b for a, b in zip(x, y)]) <= h
        fx, fy = fill(x), fill(y)
        assert distance(fx, fy) <= 6*l1([a-b for a, b in zip(x, y)])
        qx, _ = quantize(fx, bits)
        qy, _ = quantize(fy, bits)
        actual = distance(qx, qy)
        assert actual <= bound
        worst = max(worst, actual)
    sampler_outcomes = 0
    for point in points[:8]:
        out, counts = quantize(fill(point), 8)
        seen = [0]*5
        for value in range(256):
            cutoff = 0
            for key, count in enumerate(counts):
                cutoff += count
                if value < cutoff:
                    seen[key] += 1
                    break
            else:
                raise AssertionError('bounded sampler failed')
            sampler_outcomes += 1
        assert seen == counts
    return {'rational_control_points': len(points), 'quantized_ciphers': quantized,
            'exactly_preserved_dyadic_boundary_settings': boundary_exact,
            'neighbor_parameter_pairs': 1024,
            'neighbor_l1_radius': str(h), 'sampler_fair_coin_bits': bits,
            'analytic_neighbor_joint_TV_upper_bound': str(bound),
            'largest_sampled_neighbor_joint_TV': str(worst),
            'enumerated_bounded_sampler_outcomes': sampler_outcomes,
            'real_number_oracle_or_rejection_sampling_used': False}


def main():
    result = {'exact_rational_checks': checks(),
              'fill_Lipschitz_bound_joint_key_ciphertext_TV': '6 times parameter l1 distance',
              'quantized_neighbor_bound': '6h + 5/2^B',
              'perfect_privacy_and_correctness_after_quantization': True,
              'input_representation': 'four rational coordinates of zero sum and l1 norm <=1; integer precision B>=1',
              'Foundation_machine_realization_certified': False,
              'topological_four_key_lower_bound_computer_verified': False,
              'ordinary_cryptographic_security_alone_implies_neighbor_stability': False,
              'Lean_checked': False, 'newness_established': False,
              'source_sha256': {str(f.resolve()): hashlib.sha256(f.read_bytes()).hexdigest()
                                for f in (Path(__file__), DEPENDENCY)}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
