"""Noisy qubit recovery: certified mixture budgets and numerical polar repair.

General CPTP channels are represented by Kraus operators. No SDP is used:
correctness/privacy inputs are analytically valid convex-mixture upper bounds,
not numerical diamond-norm estimates. Bell-input distances only supply checked
lower bounds. Seven-key cone identities use exact rational arithmetic.
Topological claims and general inequalities are mathematical proofs in the note.
"""
from pathlib import Path
import importlib.util
from fractions import Fraction as F
from itertools import product
from random import Random
from math import sqrt, log2
import hashlib
import json

DEPENDENCY = Path(__file__).with_name('quantum-encryption-robust-retraction.py')
spec = importlib.util.spec_from_file_location('prior_qubit_repair', DEPENDENCY)
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)
mm, transpose, eye = prior.mm, prior.tr, prior.eye
I = [[1, 0], [0, 1]]
X = [[0, 1], [1, 0]]
Y = [[0, -1j], [1j, 0]]
Z = [[1, 0], [0, -1]]
PAULIS = [I, X, Y, Z]


def adj(a):
    return [[complex(x).conjugate() for x in row] for row in transpose(a)]


def scale(a, s):
    return [[s*x for x in row] for row in a]


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def unitary(q):
    a, b, c, d = q
    return [[a-1j*d, -c-1j*b], [c-1j*b, a+1j*d]]


def apply(kraus, a):
    terms = [mm(mm(k, a), adj(k)) for k in kraus]
    return [[sum(t[i][j] for t in terms) for j in range(2)] for i in range(2)]


def affine(kraus):
    outputs = [apply(kraus, p) for p in PAULIS]
    coefficients = [[trace(mm(p, out))/2 for out in outputs] for p in PAULIS]
    assert max(abs(x.imag) for row in coefficients for x in row) < 1e-10
    assert max(abs(coefficients[0][j]-int(j == 0)) for j in range(4)) < 1e-10
    return ([[coefficients[i][j].real for j in range(1, 4)] for i in range(1, 4)],
            [coefficients[i][0].real for i in range(1, 4)])


def assert_channel(kraus):
    products = [mm(adj(k), k) for k in kraus]
    total = [[sum(m[i][j] for m in products) for j in range(2)] for i in range(2)]
    assert prior.difference(total, I) < 1e-10


def choi(kraus):
    vectors = [[k[i][j] for j in range(2) for i in range(2)] for k in kraus]
    return [[sum(v[i]*complex(v[j]).conjugate() for v in vectors)/2
             for j in range(4)] for i in range(4)]


def bell_distance(a, b):
    h = [[a[i][j]-b[i][j] for j in range(4)] for i in range(4)]
    realification = [[complex(h[i % 4][j % 4]).real if (i < 4) == (j < 4)
                      else (-1 if i < 4 else 1)*complex(h[i % 4][j % 4]).imag
                      for j in range(8)] for i in range(8)]
    values, _ = prior.eigen(realification)
    return sum(abs(x) for x in values)/4


def unitary_polar(a):
    values, vectors = prior.eigen(mm(transpose(a), a))
    assert min(values) > 0
    invsqrt = mm([[vectors[i][j]/sqrt(values[j]) for j in range(3)] for i in range(3)], transpose(vectors))
    r = mm(a, invsqrt)
    assert prior.det3(r) > 0 and prior.difference(mm(transpose(r), r), eye(3)) < 1e-9
    return r, [sqrt(v) for v in values]


def quaternion(r):
    values = [1+r[0][0]+r[1][1]+r[2][2], 1+r[0][0]-r[1][1]-r[2][2],
              1-r[0][0]+r[1][1]-r[2][2], 1-r[0][0]-r[1][1]+r[2][2]]
    index = max(range(4), key=values.__getitem__)
    q = [0.0]*4
    q[index] = sqrt(max(0, values[index]))/2
    denominator = 4*q[index]
    if index == 0:
        q[1:] = [(r[2][1]-r[1][2])/denominator, (r[0][2]-r[2][0])/denominator,
                  (r[1][0]-r[0][1])/denominator]
    else:
        i = index-1
        j, k = (i+1) % 3, (i+2) % 3
        q[0] = (r[k][j]-r[j][k])/denominator
        q[j+1] = (r[j][i]+r[i][j])/denominator
        q[k+1] = (r[k][i]+r[i][k])/denominator
    assert prior.difference(prior.rotation(q), r) < 1e-9
    return q


def noisy_experiments():
    rng = Random(310882)
    success = outside = 0
    identity_choi = choi([I])
    depolarizing_choi = [[int(i == j)/4 for j in range(4)] for i in range(4)]
    worst_eta = max_translation = 0.0
    kraus_checks = unit_part_checks = 0
    for _ in range(256):
        frame = prior.rotation(prior.unit([rng.gauss(0, 1) for __ in range(4)]))
        axes = [[frame[i][j] for i in range(3)] for j in range(3)]
        exact = [unitary([1, 0, 0, 0])] + [unitary([0]+axis) for axis in axes]
        common = unitary(prior.unit([rng.gauss(0, 1) for __ in range(4)]))
        exact = [mm(common, u) for u in exact]
        raw = [rng.uniform(0.8, 1.2) for __ in range(4)]
        weights = [p/sum(raw) for p in raw]
        key_tv = sum(abs(p-0.25) for p in weights)/2
        rotations, recovery_budgets, encoder_mixture_rates = [], [], []
        encoder_chois = []
        for u in exact:
            h, b = rng.uniform(0, 0.07), rng.uniform(0, 0.035)
            rate = rng.uniform(0, 1)
            before = unitary(prior.unit([rng.gauss(0, 1) for __ in range(4)]))
            after = unitary(prior.unit([rng.gauss(0, 1) for __ in range(4)]))
            damping = [[[1, 0], [0, sqrt(1-rate)]], [[0, sqrt(rate)], [0, 0]]]
            noise = [mm(mm(after, k), before) for k in damping]
            encoder = [scale(u, sqrt(1-h))]+[scale(k, sqrt(h)) for k in noise]
            decoder = [scale(adj(u), sqrt(1-b))]+[scale(p, sqrt(b)/2) for p in PAULIS]
            assert_channel(encoder)
            assert_channel(decoder)
            kraus_checks += 2
            delta = h+b-h*b
            composition = [mm(d, e) for d in decoder for e in encoder]
            assert bell_distance(choi(composition), identity_choi) <= delta+1e-9
            a, t = affine(encoder)
            r, singular = unitary_polar(a)
            assert min(singular) >= 1-2*delta-1e-9
            assert prior.norm(t) <= 2*delta+1e-9
            assert max(singular) <= 1+1e-9
            # Spin-flip symmetrization is a separately built Kraus channel.
            unital = [scale(k, 1/sqrt(2)) for k in encoder]
            unital += [scale(mm(mm(Y, [[complex(x).conjugate() for x in row] for row in k]), Y), 1/sqrt(2)) for k in encoder]
            assert_channel(unital)
            au, tu = affine(unital)
            assert prior.difference(au, a) < 1e-10 and prior.norm(tu) < 1e-10
            unit_part_checks += 1
            signed_pauli = [(1+sum(singular))/4] + [(1+2*singular[j]-sum(singular))/4 for j in range(3)]
            assert min(signed_pauli) >= -1e-9
            certified_upper = (3-sum(singular))/4+prior.norm(t)/2
            assert certified_upper <= 2.5*delta+1e-9
            ur = unitary(quaternion(r))
            assert bell_distance(choi(encoder), choi([ur])) <= certified_upper+1e-9
            rotations.append(r)
            recovery_budgets.append(delta)
            encoder_mixture_rates.append(h)
            encoder_chois.append(choi(encoder))
            max_translation = max(max_translation, prior.norm(t))
        delta = max(recovery_budgets)
        epsilon = key_tv+sum(p*h for p, h in zip(weights, encoder_mixture_rates))
        eta = epsilon+2.5*delta
        average_choi = [[sum(p*c[i][j] for p, c in zip(weights, encoder_chois)) for j in range(4)] for i in range(4)]
        assert bell_distance(average_choi, depolarizing_choi) <= epsilon+1e-9
        normalized = [mm(transpose(rotations[0]), r) for r in rotations]
        qs = [quaternion(r) for r in normalized]
        measured_unitary_privacy = prior.privacy(qs, weights)
        assert measured_unitary_privacy <= eta+1e-8
        if eta >= 0.25-1e-10:
            outside += 1
            continue
        repaired = prior.polar_repair(qs, weights)
        assert prior.privacy(repaired) < 1e-9
        success += 1
        worst_eta = max(worst_eta, eta)
    return {'protocol_settings': success+outside, 'inside_sufficient_error_region': success,
            'outside_sufficient_error_region': outside, 'encoder_decoder_Kraus_checks': kraus_checks,
            'nonunital_symmetrization_checks': unit_part_checks,
            'largest_certified_eta_inside_region': worst_eta, 'largest_tested_translation_norm': max_translation,
            'correctness_budget': 'delta_k = h_k + b_k - h_k b_k, certified by convex mixture with identity',
            'secrecy_budget': 'TV(key law,uniform) + sum_k p_k h_k, certified by convex mixture with exact private scheme',
            'diamond_norm_SDP_performed': False,
            'Bell_input_distances_are_only_lower_bounds': True,
            'numerical_tolerance': 1e-8}


def seven_key_cone():
    fixed = [eye(3)]+[[[int(i == j)*(1 if i == axis else -1) for j in range(3)] for i in range(3)] for axis in range(3)]
    checked = 0
    for t in product(range(-1, 2), repeat=3):
        s = sum(x*x for x in t)
        q = [F(1-s, 1+s)]+[F(2*x, 1+s) for x in t]
        r = prior.rotation(q)
        original = [mm(mm(r, branch), transpose(r)) for branch in fixed]
        for step in range(17):
            lam = F(step, 16)
            weights = [F(1, 4)]+[(1-lam)/4]*3+[lam/4]*3
            branches = [eye(3)]+original[1:]+fixed[1:]
            assert sum(weights) == 1
            average = [[sum(p*b[i][j] for p, b in zip(weights, branches)) for j in range(3)] for i in range(3)]
            assert average == [[0]*3 for __ in range(3)]
            for branch in branches:
                assert mm(transpose(branch), branch) == eye(3)
            entropy = -sum(float(p)*log2(float(p)) for p in weights if p)
            assert entropy <= 2.75+1e-12
            if step == 8:
                assert entropy == 2.75
            if step == 16:
                assert all(p == 0 for p in weights[1:4])
            checked += 1
    return {'exact_rational_mixtures': checked, 'maximum_key_labels': 7,
            'entropy_upper_bound_bits': '11/4', 'extra_entropy_upper_bound_bits': '3/4',
            'zero_probability_key_branches_identified': True,
            'key_count_or_entropy_optimality_proved': False}


def boundary_retraction_checks():
    fixed = [eye(3)]+[[[int(i == j)*(1 if i == axis else -1) for j in range(3)] for i in range(3)] for axis in range(3)]
    count = 0
    for t in product(range(-1, 2), repeat=3):
        length_squared = sum(x*x for x in t)
        q = [F(1-length_squared, 1+length_squared)]+[F(2*x, 1+length_squared) for x in t]
        r = prior.rotation(q)
        branches = [mm(mm(r, d), transpose(r)) for d in fixed]
        rounded = [unitary_polar(a)[0] for a in branches]
        normalized = [mm(transpose(rounded[0]), a) for a in rounded]
        repaired = prior.polar_repair([quaternion(a) for a in normalized])
        for original, repaired_q in zip(branches, repaired):
            assert prior.difference(original, prior.rotation(repaired_q)) < 1e-9
        count += 1
    return count


def main():
    result = {'noisy_recovery_experiments': noisy_experiments(), 'seven_key_cone': seven_key_cone(),
              'exact_boundary_retraction_numerical_settings': boundary_retraction_checks(),
              'mathematical_result': 'For qubit-to-qubit encryption/recovery with per-key recovery error delta, a continuous unitary rounding has branch half-diamond distance <= (5/2)delta; epsilon+(5/2)delta<1/4 yields a retraction to normalized perfect schemes.',
              'topological_theorems_computer_verified': False, 'Lean_checked': False,
              'optimal_constants_proved': False, 'newness_established': False,
              'cryptographic_reduction_impossibility_proved': False,
              'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__), DEPENDENCY)}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
