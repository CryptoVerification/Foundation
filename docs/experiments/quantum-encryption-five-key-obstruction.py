"""Finite matrix checks supporting the five-key obstruction in the audit.

The nonextension theorem is a mathematical argument, not a consequence of these
finite checks. No singular cohomology or homotopy computation is implemented.
Only Python's standard library is used. Earlier archived sources stay frozen.
"""
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
from random import Random
from math import sqrt
import hashlib
import importlib.util
import json

DEPENDENCY = Path(__file__).with_name('quantum-encryption-robust-retraction.py')
spec = importlib.util.spec_from_file_location('frozen_repair', DEPENDENCY)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def determinant(a):
    n = len(a)
    total = F(0)
    for perm in permutations(range(n)):
        sign = (-1)**sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n))
        value = F(sign)
        for i in range(n):
            value *= a[i][perm[i]]
        total += value
    return total


def choi_pieces(a):
    return [[[F(a[i][k]*a[j][k], 4) for j in range(4)] for i in range(4)]
            for k in range(len(a[0]))]


def cartan(a, b, c):
    args = (a, b, c)
    value = 0
    for perm in permutations(range(3)):
        sign = (-1)**sum(perm[i] > perm[j] for i in range(3) for j in range(i+1, 3))
        value += sign*trace(p.mm(p.mm(args[perm[0]], args[perm[1]]), args[perm[2]]))
    return value


def generator(i, j, n=5):
    a = [[0]*n for _ in range(n)]
    a[i][j], a[j][i] = -1, 1
    return a


def exact_checks():
    # L_i v = e_i cross v on the three imaginary quaternion coordinates.
    ls = [generator(2, 3), generator(3, 1), generator(1, 2)]
    assert cartan(*ls) == -6
    twice = [[[2*x for x in row] for row in a] for a in ls]
    assert cartan(*twice) == -48  # differential of q -> Ad_q at q=1
    rng = Random(20261023)
    frames = sign_checks = permutation_checks = 0
    nonzero_fifth = zero_fifth = 0
    for case in range(32):
        o = p.eye(5)
        if case:
            for _ in range(8):
                i, j = rng.sample(range(5), 2)
                t = F(rng.randint(-4, 4), rng.randint(1, 5))
                c, s = (1-t*t)/(1+t*t), 2*t/(1+t*t)
                g = p.eye(5)
                g[i][i] = g[j][j] = c
                g[i][j], g[j][i] = -s, s
                o = p.mm(o, g)
        assert p.mm(o, p.tr(o)) == p.eye(5)
        assert determinant(o) == 1
        a = o[:4]
        pieces = choi_pieces(a)
        weights = [trace(r) for r in pieces]
        assert sum(weights) == 1 and all(0 <= w <= F(1, 4) for w in weights)
        assert [[sum(r[i][j] for r in pieces) for j in range(4)] for i in range(4)] == [
            [F(i == j, 4) for j in range(4)] for i in range(4)]
        nonzero_fifth += int(weights[4] > 0)
        zero_fifth += int(weights[4] == 0)
        for signs in product((-1, 1), repeat=5):
            d = 1
            for s in signs:
                d *= s
            # Completion of A D to SO(5) is J_det(D) O D.
            transformed = [[o[i][j]*signs[j]*(d if i == 4 else 1)
                            for j in range(5)] for i in range(5)]
            assert determinant(transformed) == 1
            assert choi_pieces(transformed[:4]) == pieces
            conj = [[[signs[i]*b[i][j]*signs[j] for j in range(5)]
                     for i in range(5)] for b in ls]
            assert cartan(*conj) == -6
            sign_checks += 1
        # Relabeling keys is an additional finite quotient, not a continuous
        # change of physical input/output coordinates. Test its generators.
        for i in range(5):
            for j in range(i+1, 5):
                perm = list(range(5))
                perm[i], perm[j] = perm[j], perm[i]
                transformed = [[o[r][perm[c]]*(-1 if r == 4 else 1)
                                for c in range(5)] for r in range(5)]
                assert determinant(transformed) == 1
                assert choi_pieces(transformed[:4]) == [pieces[k] for k in perm]
                conj = [[[b[perm[r]][perm[c]] for c in range(5)]
                         for r in range(5)] for b in ls]
                assert cartan(*conj) == -6
                permutation_checks += 1
        frames += 1
    assert nonzero_fifth > 0 and zero_fifth > 0
    # Flipping the unused fifth column fixes the padded boundary frame.
    signs = (1, 1, 1, 1, -1)
    fixed = [[int(i == j)*signs[j]*(-1 if i == 4 else 1)
              for j in range(5)] for i in range(5)]
    assert fixed == p.eye(5)
    return {'rational_SO5_frames': frames,
            'frames_with_positive_fifth_key': nonzero_fifth,
            'frames_with_zero_fifth_key': zero_fifth,
            'column_sign_completion_and_Cartan_checks': sign_checks,
            'key_transposition_completion_and_Cartan_checks': permutation_checks,
            'Cartan_form_on_so3_generators': -6,
            'boundary_pullback_on_unit_quaternion_tangents': -48,
            'finite_sign_action_has_fixed_points': True}


def whiten(a):
    gram = p.mm(a, p.tr(a))
    values, vectors = p.eigen(gram)
    assert min(values) > 0
    inverse = p.mm([[vectors[i][j]/sqrt(values[j]) for j in range(4)]
                    for i in range(4)], p.tr(vectors))
    return p.mm(inverse, a)


def numerical_checks():
    rng = Random(73119)
    repaired = sign_checks = fixed_checks = 0
    largest_residual = 0.0
    for keys in (4, 5, 6, 7, 11):
        for case in range(80):
            a = [[rng.gauss(0, 1) for _ in range(keys)] for _ in range(4)]
            if keys > 4 and case % 4 == 0:
                for row in a:
                    row[-1] = 0.0
            a = whiten(a)
            assert p.difference(whiten(a), a) < 1e-10
            fixed_checks += 1
            # Alter both weights and branch directions; total probability is 1.
            b = [[x+0.01*rng.gauss(0, 1) if x != 0 else 0.0 for x in row] for row in a]
            scale = sqrt(4/sum(x*x for row in b for x in row))
            b = [[scale*x for x in row] for row in b]
            values, _ = p.eigen(p.mm(b, p.tr(b)))
            # For unital qubit channels the Choi spectral formula equals the
            # half-diamond distance; the audit needs only its Choi lower bound.
            eps = sum(abs(x/4-0.25) for x in values)/2
            assert eps < 0.25 and min(values) >= 1-4*eps-1e-10
            out = whiten(b)
            residual = p.difference(p.mm(out, p.tr(out)), p.eye(4))
            assert residual < 1e-10
            largest_residual = max(largest_residual, residual)
            assert all(sum(out[i][j]**2 for i in range(4))/4 <= 0.25+1e-10
                       for j in range(keys))
            signs = [rng.choice((-1, 1)) for _ in range(keys)]
            signed = [[x*signs[j] for j, x in enumerate(row)] for row in b]
            expected = [[x*signs[j] for j, x in enumerate(row)] for row in out]
            assert p.difference(whiten(signed), expected) < 1e-10
            sign_checks += 1
            if keys > 4 and case % 4 == 0:
                assert all(row[-1] == 0 for row in out)
            repaired += 1
    return {'near_frame_whitening_cases': repaired,
            'exact_frame_fixed_point_cases': fixed_checks,
            'sign_equivariance_cases': sign_checks,
            'key_counts_tested': [4, 5, 6, 7, 11],
            'largest_row_orthogonality_residual': largest_residual}


def main():
    result = {'exact_rational_checks': exact_checks(),
              'numerical_checks': numerical_checks(),
              'mathematical_claim': 'The padded quaternion Pauli boundary S3 -> E5 has nonzero pullback of a real degree-three cohomology class; hence it cannot extend to B4 in E5.',
              'minimum_key_count_for_this_exact_boundary_task': '6 or 7; six keys unresolved',
              'robust_claim': 'With boundary probabilities (1/4,1/4,1/4,1/4,0) and per-positive-key boundary encryption error <=1/20, some control has privacy + (5/2) max positive-key recovery error >=1/4.',
              'topological_claim_computer_verified': False,
              'Lean_checked': False,
              'infinity_categorical_formalism_proved_necessary': False,
              'natural_protocol_application_identified': False,
              'newness_established': False,
              'source_sha256': {str(f.resolve()): hashlib.sha256(f.read_bytes()).hexdigest()
                                for f in (Path(__file__), DEPENDENCY)}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
