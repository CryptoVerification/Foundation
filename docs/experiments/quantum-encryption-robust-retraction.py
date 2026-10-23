"""Robust normalized qubit encryption: numerical polar repair and exact checks.

Numerical checks use a small symmetric Jacobi eigensolver (standard library
only), never a finite experiment as proof of a topological assertion. Exact
rational checks cover the rank-deficient quarter-distance witness and the
weighted eight-key cone of perfectly private schemes. No source from an earlier
frozen experiment is modified. Diamond distance is HALF the diamond norm.
"""
from fractions import Fraction as F
from itertools import product, permutations
from pathlib import Path
from random import Random
from math import sqrt, sin, cos, copysign, log2
import hashlib
import json


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def tr(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def difference(a, b):
    return max(abs(x-y) for ra, rb in zip(a, b) for x, y in zip(ra, rb))


def det3(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def eigen(a):
    n, original = len(a), [list(row) for row in a]
    a, v = [[float(x) for x in row] for row in a], eye(n)
    for _ in range(256):
        p, q = max(((i, j) for i in range(n) for j in range(i+1, n)),
                   key=lambda pair: abs(a[pair[0]][pair[1]]))
        off = a[p][q]
        if abs(off) < 1e-14:
            break
        tau = (a[q][q]-a[p][p])/(2*off)
        t = copysign(1.0, tau)/(abs(tau)+sqrt(1+tau*tau))
        c, s = 1/sqrt(1+t*t), t/sqrt(1+t*t)
        a[p][p], a[q][q] = a[p][p]-t*off, a[q][q]+t*off
        a[p][q] = a[q][p] = 0.0
        for k in range(n):
            if k not in (p, q):
                x, y = a[k][p], a[k][q]
                a[k][p] = a[p][k] = c*x-s*y
                a[k][q] = a[q][k] = s*x+c*y
            x, y = v[k][p], v[k][q]
            v[k][p], v[k][q] = c*x-s*y, s*x+c*y
    else:
        raise AssertionError('Jacobi solver did not converge')
    values = [a[i][i] for i in range(n)]
    diagonal = [[values[i] if i == j else 0 for j in range(n)] for i in range(n)]
    residual = difference(mm(original, v), mm(v, diagonal))
    assert residual < 1e-10 and difference(mm(tr(v), v), eye(n)) < 1e-10
    return values, v


def norm(q):
    return sqrt(sum(x*x for x in q))


def unit(q):
    length = norm(q)
    return [x/length for x in q]


def rotation(q):
    a, b, c, d = q
    return [[1-2*(c*c+d*d), 2*(b*c-a*d), 2*(b*d+a*c)],
            [2*(b*c+a*d), 1-2*(b*b+d*d), 2*(c*d-a*b)],
            [2*(b*d-a*c), 2*(c*d+a*b), 1-2*(b*b+c*c)]]


def gram_choi(qs, weights=None):
    if weights is None:
        weights = [0.25]*4
    return [[sum(p*q[i]*q[j] for p, q in zip(weights, qs)) for j in range(4)] for i in range(4)]


def privacy(qs, weights=None):
    values, _ = eigen(gram_choi(qs, weights))
    # Unital-qubit canonical form + Pauli-channel norm formula justify equality.
    return sum(abs(x-0.25) for x in values)/2


def polar_repair(qs, weights=None):
    if weights is None:
        weights = [0.25]*4
    v = [[2*sqrt(weights[j+1])*qs[j+1][i+1] for j in range(3)] for i in range(3)]
    values, vectors = eigen(mm(tr(v), v))
    assert min(values) > 0
    inverse_sqrt = mm([[vectors[i][j]/sqrt(values[j]) for j in range(3)] for i in range(3)], tr(vectors))
    w = mm(v, inverse_sqrt)
    assert difference(mm(tr(w), w), eye(3)) < 1e-10
    return [[1.0, 0.0, 0.0, 0.0]] + [[0.0]+[w[i][j] for i in range(3)] for j in range(3)]


def numerical_checks():
    rng = Random(18277)
    accepted = rejected = covariance = signs = 0
    worst_bound_slack = 1.0
    for _ in range(640):
        frame = rotation(unit([rng.gauss(0, 1) for __ in range(4)]))
        scale = rng.choice((0.001, 0.02, 0.1, 0.25, 0.5, 0.9))
        qs = [[1.0, 0.0, 0.0, 0.0]]
        for j in range(3):
            axis = unit([frame[i][j]+scale*rng.gauss(0, 1) for i in range(3)])
            angle = scale*rng.uniform(-1, 1)
            qs.append([sin(angle)]+[cos(angle)*x for x in axis])
        eps = privacy(qs)
        if eps >= 0.25-1e-10:
            rejected += 1
            continue
        accepted += 1
        repaired = polar_repair(qs)
        assert privacy(repaired) < 1e-10
        cvalues, _ = eigen(gram_choi(qs))
        assert min(cvalues) >= 0.25-eps-1e-10
        v = [[qs[j+1][i+1] for j in range(3)] for i in range(3)]
        vvalues, _ = eigen(mm(tr(v), v))
        assert min(vvalues) >= 1-4*eps-1e-10
        for q, r in zip(qs, repaired):
            # For SU(2) channels the half-diamond distance squared is 1-dot(q,r)^2.
            distance_squared = max(0.0, 1-sum(x*y for x, y in zip(q, r))**2)
            slack = 4*eps-distance_squared
            assert slack > -1e-10
            worst_bound_slack = min(worst_bound_slack, slack)
        if accepted % 16 == 0:
            for perm, sign in product(permutations(range(3)), product((-1, 1), repeat=3)):
                transformed = [qs[0]] + [[sign[j]*x for x in qs[1+perm[j]]] for j in range(3)]
                rr = polar_repair(transformed)
                expected = [repaired[0]] + [[sign[j]*x for x in repaired[1+perm[j]]] for j in range(3)]
                assert difference(rr, expected) < 1e-9
                signs += 1
        common = rotation(unit([rng.gauss(0, 1) for __ in range(4)]))
        def conjugate(q):
            return [q[0]]+[sum(common[i][j]*q[j+1] for j in range(3)) for i in range(3)]
        rr = polar_repair([conjugate(q) for q in qs])
        assert difference(rr, [conjugate(q) for q in repaired]) < 1e-9
        covariance += 1
        # An independently obtained canonical Pauli form from the Bloch matrix.
        bloch = [[sum(rotation(q)[i][j] for q in qs)/4 for j in range(3)] for i in range(3)]
        sv2, _ = eigen(mm(tr(bloch), bloch))
        singular = sorted((sqrt(max(0, value)) for value in sv2), reverse=True)
        signed = singular[:2] + [copysign(singular[2], det3(bloch))]
        x, y, z = signed
        probabilities = [(1+x+y+z)/4, (1+x-y-z)/4, (1-x+y-z)/4, (1-x-y+z)/4]
        assert min(probabilities) > -1e-9
        assert abs(eps-sum(abs(p-0.25) for p in probabilities)/2) < 1e-8
    return {'sampled_schemes': accepted+rejected, 'below_quarter_distance': accepted,
            'outside_guaranteed_neighborhood': rejected,
            'sign_and_key_permutation_covariance_checks': signs,
            'common_basis_covariance_checks': covariance,
            'eigen_residual_tolerance': 1e-10,
            'independent_privacy_comparison_tolerance': 1e-8,
            'minimum_observed_squared_repair_bound_slack': worst_bound_slack}


def weighted_checks():
    rng = Random(7732)
    accepted = rejected = 0
    for _ in range(384):
        frame = rotation(unit([rng.gauss(0, 1) for __ in range(4)]))
        scale = rng.choice((0.005, 0.03, 0.1, 0.25, 0.6))
        qs = [[1.0, 0.0, 0.0, 0.0]]
        for j in range(3):
            axis = unit([frame[i][j]+scale*rng.gauss(0, 1) for i in range(3)])
            angle = scale*rng.uniform(-1, 1)
            qs.append([sin(angle)]+[cos(angle)*x for x in axis])
        raw_weights = [rng.uniform(0.1, 1.0) for __ in range(4)]
        weights = [w/sum(raw_weights) for w in raw_weights]
        eps = privacy(qs, weights)
        if eps >= 0.25-1e-10:
            rejected += 1
            continue
        accepted += 1
        assert min(weights) >= 0.25-eps-1e-10
        assert max(weights) <= 0.25+eps+1e-10
        repaired = polar_repair(qs, weights)
        assert privacy(repaired) < 1e-10
        for q, r in zip(qs, repaired):
            distance_squared = max(0.0, 1-sum(x*y for x, y in zip(q, r))**2)
            assert distance_squared <= 8*eps/(1+4*eps)+1e-10
        sign = (-1, 1, -1)
        perm = (2, 0, 1)
        transformed = [qs[0]] + [[sign[j]*x for x in qs[1+perm[j]]] for j in range(3)]
        transformed_weights = [weights[0]]+[weights[1+perm[j]] for j in range(3)]
        rr = polar_repair(transformed, transformed_weights)
        expected = [repaired[0]] + [[sign[j]*x for x in repaired[1+perm[j]]] for j in range(3)]
        assert difference(rr, expected) < 1e-9
    return {'sampled_schemes': accepted+rejected, 'below_quarter_distance': accepted,
            'outside_guaranteed_neighborhood': rejected,
            'biased_four_key_laws_supported': True,
            'key_probability_and_squared_repair_bounds_checked': True}


def exact_checks():
    critical_gram = [[F(1) if i == j else F(1, 3) if i == 0 or j == 0 else F(-1, 3)
                      for j in range(4)] for i in range(4)]
    assert mm(critical_gram, critical_gram) == [[F(4, 3)*x for x in row] for row in critical_gram]
    kernel = [[-1], [1], [1], [1]]
    assert mm(critical_gram, kernel) == [[0]]*4
    critical_pauli = [F(1, 3), F(1, 3), F(1, 3), F(0)]
    assert sum(abs(p-F(1, 4)) for p in critical_pauli)/2 == F(1, 4)
    fixed = [eye(3)] + [[[int(i == j)*(1 if i == axis else -1) for j in range(3)]
                        for i in range(3)] for axis in range(3)]
    mixtures = 0
    for t in product(range(-1, 2), repeat=3):
        s = sum(x*x for x in t)
        q = [F(1-s, 1+s)] + [F(2*x, 1+s) for x in t]
        r = rotation(q)
        original = [mm(mm(r, branch), tr(r)) for branch in fixed]
        for step in range(17):
            lam = F(step, 16)
            weights = [(1-lam)/4]*4 + [lam/4]*4
            branches = original+fixed
            average = [[sum(p*b[i][j] for p, b in zip(weights, branches)) for j in range(3)] for i in range(3)]
            assert average == [[0]*3 for _ in range(3)]
            for b in branches:
                assert mm(tr(b), b) == eye(3)
            entropy = -sum(float(p)*log2(float(p)) for p in weights if p)
            assert entropy <= 3+1e-12
            weighted = [[[p*x for x in row] for row in b] for p, b in zip(weights, branches)]
            if step == 16:
                assert weighted == [[[0]*3 for _ in range(3)]]*4 + [[[F(x, 4) for x in row] for row in b] for b in fixed]
            mixtures += 1
    return {'rank_deficient_critical_gram_exact': True,
            'rank_deficient_critical_half_diamond_distance': '1/4',
            'eight_key_exact_mixtures_checked': mixtures,
            'entropy_upper_bound_bits': 3,
            'endpoint_independence_checked_as_weighted_branches': True}


def main():
    out = {'numerical_polar_repair': numerical_checks(), 'biased_four_key_repair': weighted_checks(), 'exact_rational_checks': exact_checks(),
           'scope': 'normalized qubit unitary branches, four possibly biased keys for robust repair; up to eight weighted keys for the exact-private cone',
           'privacy_metric': 'one half of diamond-norm distance to the completely depolarizing channel, including arbitrary reference systems',
           'mathematical_claim': 'For epsilon < 1/4 a continuous sign-independent polar retraction to exact schemes exists; uniform keys have branch distance at most 2 sqrt(epsilon), biased keys at most sqrt(8 epsilon / (1+4 epsilon)).',
           'quarter_threshold_for_global_nullhomotopy_proved_sharp': False,
           'topological_theorems_computer_verified': False,
           'Lean_checked': False, 'newness_established': False,
           'cryptographic_reduction_impossibility_proved': False,
           'source_sha256': {str(Path(__file__)): hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}}
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
