"""Exact matrix checks for five-key stabilization and the doubling homotopy.

The global five-key existence proof uses a nullhomotopy supplied by the known
order-two homotopy class. This program implements the preceding explicit
SO(5) homotopy and the frame-to-cipher algebra, not that final nullhomotopy.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import importlib.util
import json

DEPENDENCY = Path(__file__).with_name('quantum-encryption-torsion-bundle.py')
spec = importlib.util.spec_from_file_location('frozen_torsion_bundle', DEPENDENCY)
t = importlib.util.module_from_spec(spec)
spec.loader.exec_module(t)
b, p = t.b, t.b.p


def extended_left(q):
    out = p.eye(5)
    left = b.left(q)
    for i in range(4):
        for j in range(4):
            out[i][j] = left[i][j]
    return out


def conjugator(c, s):
    assert c*c+s*s == 1
    out = p.eye(5)
    for i, j in ((1, 2), (3, 4)):
        out[i][i] = out[j][j] = c
        out[i][j], out[j][i] = -s, s
    return out


def deformation(q, c, s):
    l, conjugation = extended_left(q), conjugator(c, s)
    return p.mm(p.mm(p.mm(l, conjugation), l), p.tr(conjugation))


def weighted_bloch(column):
    # Column norm squared / 4 is its probability. This polynomial remains
    # valid at zero columns, without choosing a normalized unitary there.
    a, x, y, z = column
    return [[(a*a+x*x-y*y-z*z)/4, (x*y-a*z)/2, (x*z+a*y)/2],
            [(x*y+a*z)/2, (a*a-x*x+y*y-z*z)/4, (y*z-a*x)/2],
            [(x*z-a*y)/2, (y*z+a*x)/2, (a*a-x*x-y*y+z*z)/4]]


def checks():
    directions = []
    for v in product(range(-1, 2), repeat=3):
        length = sum(x*x for x in v)
        directions.append([F(1-length, 1+length)]+[F(2*x, 1+length) for x in v])
    latitudes = [(F(1), F(0)), (F(3, 5), F(4, 5)), (F(0), F(1)),
                 (-F(3, 5), F(4, 5)), (-F(1), F(0))]
    quaternions = []
    for q, (a, r) in product(directions, latitudes):
        quaternions.append(t.suspended_hopf(a, [r*x for x in q]))
    # Also sample a general quaternion not restricted to the chosen clutch.
    quaternions += directions
    endpoints = samples = positive_fifth = 0
    for q in quaternions:
        first = deformation(q, F(1), F(0))
        assert first == extended_left(b.qm(q, q))
        last = deformation(q, F(-1), F(0))
        expected = p.eye(5)
        rotation = p.rotation(q)
        for i in range(3):
            for j in range(3):
                expected[i+1][j+1] = rotation[i][j]
        assert last == expected
        endpoints += 1
        for c, s in latitudes:
            o = deformation(q, c, s)
            assert p.mm(o, p.tr(o)) == p.eye(5)
            frame = o[:4]
            assert p.mm(frame, p.tr(frame)) == p.eye(4)
            columns = p.tr(frame)
            weights = [sum(x*x for x in col)/4 for col in columns]
            assert sum(weights) == 1 and all(0 <= w <= F(1, 4) for w in weights)
            average = [[sum(weighted_bloch(col)[i][j] for col in columns)
                        for j in range(3)] for i in range(3)]
            assert average == [[0]*3 for _ in range(3)]
            choi = [[sum(col[i]*col[j] for col in columns)/4
                     for j in range(4)] for i in range(4)]
            assert choi == [[F(i == j, 4) for j in range(4)] for i in range(4)]
            positive_fifth += int(weights[-1] > 0)
            samples += 1
    assert positive_fifth > 0
    return {'clutch_and_general_quaternion_endpoint_pairs': endpoints,
            'exact_SO5_homotopy_and_five_key_frame_samples': samples,
            'samples_with_positive_fifth_key': positive_fifth,
            'start': 'left multiplication by q squared, with one extra real coordinate',
            'end': 'diag(1, Ad_q, 1)',
            'weighted_cipher_average_Bloch_matrix': 'zero',
            'weighted_cipher_Choi_matrix': 'I4/4'}


def main():
    result = {'exact_rational_checks': checks(),
              'mathematical_sufficient_condition': 'If T(E) direct-sum two trivial real lines is trivial, E has a continuous perfectly private, exactly recoverable five-key encryption.',
              'doubling_formula': '[diag(1, Ad_g, 1)] = 2 [extended_left(g)] in pi_r(SO5).',
              'order_two_clutch_consequence': 'For every r>=2 and nonzero clutch g of order two, the minimum classical key alphabet is exactly five.',
              'S5_suspended_Hopf_minimum_key_count': 5,
              'entropy_upper_bound_bits': 'log2(5)',
              'global_five_key_controller_implemented': False,
              'explicit_doubling_homotopy_implemented': True,
              'nullhomotopy_of_squared_clutch_implemented': False,
              'topological_existence_theorem_computer_verified': False,
              'condition_claimed_necessary_for_all_five_key_implementations': False,
              'infinity_categorical_formalism_proved_indispensable': False,
              'Lean_checked': False, 'newness_established': False,
              'source_sha256': {str(f.resolve()): hashlib.sha256(f.read_bytes()).hexdigest()
                                for f in (Path(__file__), DEPENDENCY, t.DEPENDENCY, b.DEPENDENCY)}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
