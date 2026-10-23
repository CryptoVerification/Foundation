"""Exact quaternionic code-bundle matrices and a seven-key encryption section.

Complex four-dimensional matrices are represented faithfully as real 8x8
matrices, using left quaternion multiplication and a commuting right complex
structure. The ground projector has real rank 4, hence complex rank 2.
Finite algebra checks do not verify the topological nonsection theorem.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import importlib.util
import json

DEPENDENCY = Path(__file__).with_name('quantum-encryption-robust-retraction.py')
spec = importlib.util.spec_from_file_location('bundle_matrix_helpers', DEPENDENCY)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)


def qm(q, r):
    a, b, c, d = q
    e, f, g, h = r
    return [a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e]


def conjugate(q):
    return [q[0]]+[-x for x in q[1:]]


def left(q):
    return p.tr([qm(q, e) for e in p.eye(4)])


def scale(a, s):
    return [[s*x for x in row] for row in a]


def add(a, b):
    return [[x+y for x, y in zip(r, s)] for r, s in zip(a, b)]


def block(a, b, c, d):
    return [r+s for r, s in zip(a, b)]+[r+s for r, s in zip(c, d)]


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


I4, I8 = p.eye(4), p.eye(8)
ZERO = [[0]*4 for _ in range(4)]
UNITS = p.eye(4)[1:]
LI = [left(e) for e in UNITS]
# Right multiplication by i commutes with every left quaternion matrix.
JR = p.tr([qm(e, UNITS[0]) for e in p.eye(4)])
J8 = block(JR, ZERO, ZERO, JR)
SIGMA = [p.mm(JR, a) for a in LI]


def data(t, s, q):
    assert t*t+s*s == 1 and sum(x*x for x in q) == 1
    y = [s*x for x in q]
    h = block(scale(I4, t), left(y), left(conjugate(y)), scale(I4, -t))
    projector = scale(add(I8, h), F(1, 2))
    # The physical Hamiltonian is -h, so projector is its ground space.
    n = scale(I4, 1+t)+left(conjugate(y)) if t != -1 else None
    south = left(y)+scale(I4, 1-t) if t != 1 else None
    return h, projector, n, south


def local_gates(frame, denominator, projector):
    complement = add(I8, scale(projector, -1))
    return [add(scale(p.mm(p.mm(frame, a), p.tr(frame)), 1/denominator), complement)
            for a in LI]


def compile_point(t, s, q):
    h, projector, n, south = data(t, s, q)
    w_n, w_s = (1+t)/2, (1-t)/2
    # Operators on zero-probability keys are placeholders, not continuous gates.
    north_gates = local_gates(n, 2*(1+t), projector) if n is not None else [I8]*3
    south_gates = local_gates(south, 2*(1-t), projector) if south is not None else [I8]*3
    return [F(1, 4)]+[w_n/4]*3+[w_s/4]*3, [I8]+north_gates+south_gates


def exact_checks():
    for a in LI:
        assert p.mm(a, JR) == p.mm(JR, a)
    for b in SIGMA:
        assert b == p.tr(b) and p.mm(b, b) == I4 and trace(b) == 0
    directions = []
    for v in product(range(-1, 2), repeat=3):
        length = sum(x*x for x in v)
        directions.append([F(1-length, 1+length)]+[F(2*x, 1+length) for x in v])
    latitudes = [(F(1), F(0)), (F(3, 5), F(4, 5)), (F(0), F(1)),
                 (-F(3, 5), F(4, 5)), (-F(1), F(0))]
    cases = overlaps = branch_checks = privacy_checks = 0
    for q, (t, s) in product(directions, latitudes):
        h, projector, n, south = data(t, s, q)
        assert h == p.tr(h) and p.mm(h, h) == I8 and trace(h) == 0
        assert p.mm(projector, projector) == projector and trace(projector) == 4
        assert p.mm(h, J8) == p.mm(J8, h)
        if n is not None:
            assert p.mm(p.tr(n), n) == scale(I4, 2*(1+t))
            assert scale(p.mm(n, p.tr(n)), 1/(2*(1+t))) == projector
        if south is not None:
            assert p.mm(p.tr(south), south) == scale(I4, 2*(1-t))
            assert scale(p.mm(south, p.tr(south)), 1/(2*(1-t))) == projector
        if n is not None and south is not None:
            # Unnormalized frames differ by s/(1+t) times left(q).
            assert south == scale(p.mm(n, left(q)), s/(1+t))
            north_gates = local_gates(n, 2*(1+t), projector)
            for i, u in enumerate(local_gates(south, 2*(1-t), projector)):
                local = scale(p.mm(p.mm(p.tr(n), u), n), 1/(2*(1+t)))
                assert local == p.mm(p.mm(left(q), LI[i]), left(conjugate(q)))
            overlaps += 1
        weights, gates = compile_point(t, s, q)
        assert sum(weights) == 1 and min(weights) >= 0
        for w, gate in zip(weights, gates):
            if not w:
                continue
            assert p.mm(p.tr(gate), gate) == I8
            assert p.mm(gate, projector) == p.mm(projector, gate)
            assert p.mm(gate, J8) == p.mm(J8, gate)
            branch_checks += 1
        frame, denominator = (n, 2*(1+t)) if n is not None else (south, 2*(1-t))
        # Check the channel on a complete logical Hermitian basis. For I the
        # target is P; for the three traceless Pauli matrices it is zero.
        for i, b in enumerate([I4]+SIGMA):
            physical = scale(p.mm(p.mm(frame, b), p.tr(frame)), 1/denominator)
            target = projector if i == 0 else [[0]*8 for _ in range(8)]
            average = [[F(0)]*8 for _ in range(8)]
            for w, gate in zip(weights, gates):
                if w:
                    average = add(average, scale(p.mm(p.mm(gate, physical), p.tr(gate)), w))
            assert average == target
            privacy_checks += 1
        cases += 1
    return {'rational_parameter_points': cases, 'chart_overlap_points': overlaps,
            'positive_probability_unitary_branch_checks': branch_checks,
            'logical_Hermitian_basis_privacy_checks': privacy_checks,
            'physical_complex_dimension': 4, 'logical_complex_dimension': 2,
            'ground_projector_real_trace': 4,
            'chart_transition': 'q=y/|y| acts by left quaternion multiplication',
            'zero_probability_gates_identified': True}


def main():
    result = {'exact_rational_checks': exact_checks(),
              'mathematical_claim': 'The rank-two quaternionic Hopf ground-space bundle on S4 has no continuous perfectly private and exactly recoverable implementation with at most five classical keys, but has a seven-key implementation.',
              'robust_mathematical_claim': 'Every continuous five-key code-preserving implementation has a parameter with privacy + (5/2) maximum positive-key recovery error >=1/4, without an externally prescribed boundary cipher.',
              'Hamiltonian_energy_levels': [-1, 1], 'spectral_gap': 2,
              'seven_key_entropy_upper_bound_bits': '11/4',
              'topological_nonsection_claim_computer_verified': False,
              'cryptographic_protocol_in_the_cited_experiment': False,
              'digital_gate_synthesis_implemented': False,
              'infinity_categorical_formalism_necessary': False,
              'Lean_checked': False, 'newness_established': False,
              'source_sha256': {str(f.resolve()): hashlib.sha256(f.read_bytes()).hexdigest()
                                for f in (Path(__file__), DEPENDENCY)}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
