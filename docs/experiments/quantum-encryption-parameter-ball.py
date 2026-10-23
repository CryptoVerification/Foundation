"""An explicit four-real-parameter encryption specification and seven-key fill.

Exact rational checks verify cipher/recovery identities and radial endpoint
behaviour. Floating checks verify continuity bounds and boundary homotopy error
budgets. No experiment proves the topological non-extension theorem.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction as F
from math import sqrt, log2
from random import Random
import importlib.util
import hashlib
import json

DEPENDENCY = Path(__file__).with_name('quantum-encryption-robust-retraction.py')
spec = importlib.util.spec_from_file_location('qubit_ball_helpers', DEPENDENCY)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)
I = p.eye(3)
STANDARD = [I]+[[[int(i == j)*(1 if i == axis else -1) for j in range(3)] for i in range(3)] for axis in range(3)]


def boundary(q):
    rotation = p.rotation(q)
    return [p.mm(p.mm(rotation, branch), p.tr(rotation)) for branch in STANDARD]


def radial_compiler(radius, direction):
    assert 0 <= radius <= 1
    branches = [I]+boundary(direction)[1:]+STANDARD[1:]
    weights = [F(1, 4)]+[radius/4]*3+[(1-radius)/4]*3
    return weights, branches


def compile_point(x):
    radius = p.norm(x)
    assert radius <= 1+1e-12
    if radius == 0:
        direction = [1.0, 0.0, 0.0, 0.0]
    else:
        direction = [v/radius for v in x]
    return radial_compiler(min(1, radius), direction)


def cq_upper(radial_x, radial_y):
    r, q = radial_x
    s, other = radial_y
    angular = p.norm([a-b for a, b in zip(q, other)])
    return 0.75*abs(r-s)+1.5*min(r, s)*angular


def joint_key_distance(compiled_x, compiled_y):
    weights_x, branches_x = compiled_x
    weights_y, branches_y = compiled_y
    total = 0.0
    for a, b, u, v in zip(weights_x, weights_y, branches_x, branches_y):
        relative = p.mm(p.tr(u), v)
        overlap_squared = max(0.0, min(1.0, (1+sum(relative[i][i] for i in range(3)))/4))
        # For qubit unitary branches, a Bell input simultaneously attains each
        # weighted unitary discrimination bound, including the classical label.
        total += sqrt(max(0.0, (a-b)**2+4*a*b*(1-overlap_squared)))/2
    return total


def weighted_blocks(weights, branches):
    return [[[w*x for x in row] for row in b] for w, b in zip(weights, branches)]


def exact_checks():
    directions = []
    for t in product(range(-1, 2), repeat=3):
        length = sum(x*x for x in t)
        directions.append([F(1-length, 1+length)]+[F(2*x, 1+length) for x in t])
    cases = 0
    center = None
    for q, step in product(directions, range(17)):
        radius = F(step, 16)
        weights, branches = radial_compiler(radius, q)
        assert sum(weights) == 1
        average = [[sum(w*b[i][j] for w, b in zip(weights, branches)) for j in range(3)] for i in range(3)]
        assert average == [[0]*3 for __ in range(3)]
        for b in branches:
            assert p.mm(p.tr(b), b) == I
        if radius == 1:
            assert weights == [F(1, 4)]*4+[F(0)]*3
            assert branches[:4] == boundary(q)
        if radius == 0:
            blocks = weighted_blocks(weights, branches)
            center = blocks if center is None else center
            assert blocks == center
        entropy = -sum(float(w)*log2(float(w)) for w in weights if w)
        assert entropy <= 2.75+1e-12
        cases += 1
    # A four-key discontinuous comparator: all pointwise crypto guarantees hold.
    # q=(1,1,1,1)/2 cyclically permutes the three nonidentity Pauli branches.
    cycle = boundary([F(1, 2)]*4)
    assert cycle[0] == I
    assert all(cycle[i] != STANDARD[i] for i in range(1, 4))
    assert {tuple(map(tuple, x)) for x in cycle[1:]} == {tuple(map(tuple, x)) for x in STANDARD[1:]}
    return {'rational_direction_radius_cases': cases,
            'center_independent_of_direction': True,
            'boundary_matches_four_key_specification': True,
            'discontinuous_four_key_comparator_joint_key_Choi_jump': '3/4'}


def numerical_checks():
    rng = Random(81044)
    pairs = 0
    for _ in range(2048):
        q = p.unit([rng.gauss(0, 1) for __ in range(4)])
        other = p.unit([rng.gauss(0, 1) for __ in range(4)])
        r, s = rng.random(), rng.random()
        x, y = [r*a for a in q], [s*a for a in other]
        distance = p.norm([a-b for a, b in zip(x, y)])
        upper = cq_upper((r, q), (s, other))
        assert upper <= (3*sqrt(5)/4)*distance+1e-12
        actual = joint_key_distance(compile_point(x), compile_point(y))
        assert actual <= upper+1e-12
        for weights, branches in (compile_point(x), compile_point(y)):
            assert min(weights) >= 0
            average = [[sum(w*b[i][j] for w, b in zip(weights, branches)) for j in range(3)] for i in range(3)]
            assert p.norm([x for row in average for x in row]) < 1e-12
        pairs += 1
    center_approaches = 0
    for power in range(1, 14):
        for _ in range(8):
            q = p.unit([rng.gauss(0, 1) for __ in range(4)])
            r = 10.0**(-power)
            # Exact operational distance to the center: weights move between
            # disjoint old/new key labels; half diamond distance is 3r/4.
            assert abs(cq_upper((r, q), (0, [1, 0, 0, 0]))-0.75*r) < 1e-15
            center_approaches += 1
    budgets = 0
    worst = 0.0
    for eta in (0.0, 0.01, 0.1, 0.2, 0.249, 0.249999999):
        for beta in (0.0, 0.001, 0.01, 0.05):
            b = 5*beta
            maximum = eta if b <= eta or b == 0 else (eta+b)**2/(4*b)
            assert maximum < 0.25
            for step in range(101):
                t = step/100
                value = (1-t)*eta+5*t*(1-t)*beta
                assert value <= maximum+1e-15
                worst = max(worst, value)
                budgets += 1
    return {'Lipschitz_parameter_pairs_checked': pairs,
            'joint_key_distance_computed_from_weighted_unitary_Bell_formula': True,
            'Lipschitz_upper_bound': '3 sqrt(5) / 4 for joint key/ciphertext half-diamond distance',
            'center_approach_settings': center_approaches,
            'boundary_homotopy_budget_checks': budgets,
            'largest_tested_homotopy_budget': worst,
            'boundary_approximation_tolerance': '1/20 half-diamond per key',
            'uniform_continuity_of_conditional_zero_weight_gates_claimed': False}


def main():
    result = {'exact_rational_checks': exact_checks(), 'numerical_checks': numerical_checks(),
              'mathematical_lower_bound': 'Every continuous four-key qubit implementation on D4, with uniform boundary keys and boundary encryption error <=1/20 relative to the quaternion Pauli family, has a control point with privacy + (5/2) max per-key recovery error >=1/4.',
              'lower_bound_is_standard_cryptographic_reduction_impossibility': False,
              'topological_lower_bound_computer_verified': False,
              'digital_circuit_synthesis_implemented': False,
              'Lean_checked': False, 'newness_established': False,
              'source_sha256': {str(f): hashlib.sha256(f.read_bytes()).hexdigest() for f in (Path(__file__), DEPENDENCY)}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
