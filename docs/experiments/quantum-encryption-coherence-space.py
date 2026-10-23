"""Exact algebra underlying the normalized one-qubit encryption space.

Unitary qubit channels act as SO(3) rotations on Bloch vectors. A uniform
four-key channel with first branch identity is perfectly private exactly when
its other three branches are half-turns about orthogonal unoriented axes.
The topology SO(3)/D2 = S3/Q8 and the Serre-theorem consequence are mathematical
arguments, not facts established by these finite algebra checks.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json

I = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
D2 = tuple(tuple(tuple(signs[i] if i == j else 0 for j in range(3)) for i in range(3))
           for signs in product((-1, 1), repeat=3) if signs[0] * signs[1] * signs[2] == 1)
Q8 = tuple(tuple(sign * int(i == coordinate) for i in range(4))
           for coordinate in range(4) for sign in (-1, 1))


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def transpose(a):
    return tuple(zip(*a))


def det(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def mul_quaternion(q, r):
    a, b, c, d = q
    w, x, y, z = r
    return (a*w - b*x - c*y - d*z,
            a*x + b*w + c*z - d*y,
            a*y - b*z + c*w + d*x,
            a*z + b*y - c*x + d*w)


def rotation(q):
    a, b, c, d = q
    assert sum(v*v for v in q) == 1
    return ((1-2*(c*c+d*d), 2*(b*c-a*d), 2*(b*d+a*c)),
            (2*(b*c+a*d), 1-2*(b*b+d*d), 2*(c*d-a*b)),
            (2*(b*d-a*c), 2*(c*d+a*b), 1-2*(b*b+c*c)))


def encryption(r):
    # Preserve key labels 0,1,2,3. Each nonidentity branch is a half-turn.
    standard = [tuple(tuple((1 if i == axis else -1) if i == j else 0
                            for j in range(3)) for i in range(3)) for axis in range(3)]
    return (I,) + tuple(mm(mm(r, diagonal), transpose(r)) for diagonal in standard)


def main():
    points = []
    for t in product(range(-2, 3), repeat=3):
        s = sum(x*x for x in t)
        points.append((F(1-s, 1+s),) + tuple(F(2*x, 1+s) for x in t))
    points.append((F(-1), F(0), F(0), F(0)))
    stabilizers = branch_inverse_checks = 0
    for q in points:
        r = rotation(q)
        assert mm(r, transpose(r)) == I and det(r) == 1
        scheme = encryption(r)
        for branch in scheme:
            assert mm(transpose(branch), branch) == I and det(branch) == 1
            branch_inverse_checks += 1
        average = tuple(tuple(sum(branch[i][j] for branch in scheme) / F(4)
                              for j in range(3)) for i in range(3))
        assert average == ((0, 0, 0),) * 3
        # This vanishing Bloch linear map is the completely depolarizing channel.
        for h in Q8:
            rh = rotation(mul_quaternion(q, h))
            assert encryption(rh) == scheme
            assert mm(transpose(r), rh) in D2
            stabilizers += 1
    equal_pairs = distinct_pairs = 0
    for q, other in product(points, repeat=2):
        r, s = rotation(q), rotation(other)
        same = encryption(r) == encryption(s)
        assert same == (mm(transpose(r), s) in D2)
        equal_pairs += same
        distinct_pairs += not same
    source = Path(__file__)
    print(json.dumps({
        'rational_unit_quaternions_checked': len(points),
        'key_branch_correctness_checks': branch_inverse_checks,
        'perfect_privacy_Bloch_map_checks': len(points),
        'Q8_right_action_invariance_checks': stabilizers,
        'pairwise_stabilizer_fiber_checks': equal_pairs + distinct_pairs,
        'equal_normalized_scheme_pairs': equal_pairs,
        'distinct_normalized_scheme_pairs': distinct_pairs,
        'mathematical_space_identification': 'labelled, uniform four-key, no-ancilla qubit unitary encryption with identity first branch: SO(3)/D2 homeomorphic to S3/Q8',
        'mathematical_high_degree_obstruction': 'For each prime p, the p-primary component of pi_(2p) of this space is Z/p, by the covering map and Serre 1953 Chapter IV Proposition 7.',
        'topological_classification_computer_verified': False,
        'Lean_checked': False,
        'cryptographic_reduction_impossibility_proved': False,
        'requires_infinity_categories_instead_of_other_topology_formalisms': False,
        'newness_established': False,
        'source_sha256': {str(source): hashlib.sha256(source.read_bytes()).hexdigest()},
    }, indent=2))


if __name__ == '__main__':
    main()
