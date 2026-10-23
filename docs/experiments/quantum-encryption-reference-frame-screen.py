"""Exact finite algebra for screening a reference-frame application.

All distances are half diamond distances. For Pauli channels these are exactly
half the l1 distance of their probability vectors. Finite checks do not prove
the general covariance, recovery, or topological theorems. The audit supplies
the analytical argument and marks the reference-frame application as rejected
for demonstrating a need for higher categorical information.
"""
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
from random import Random
import hashlib
import json


def rotations():
    result = []
    for perm in permutations(range(3)):
        parity = (-1)**sum(perm[i] > perm[j] for i in range(3) for j in range(i+1, 3))
        for signs in product((-1, 1), repeat=3):
            if parity*signs[0]*signs[1]*signs[2] == 1:
                result.append([[signs[i]*int(j == perm[i]) for j in range(3)] for i in range(3)])
    assert len(result) == 24
    return result


def commutant_check():
    # Unknowns are the nine entries of the affine Bloch matrix A followed by t.
    rows = []
    for r in rotations():
        for i in range(3):
            for j in range(3):
                row = [F(0)]*12
                for k in range(3):
                    row[3*i+k] += r[k][j]
                    row[3*k+j] -= r[i][k]
                rows.append(row)
        for i in range(3):
            row = [F(0)]*12
            for j in range(3):
                row[9+j] = F(r[i][j]-int(i == j))
            rows.append(row)
    rank, pivots = 0, []
    for col in range(12):
        pivot = next((k for k in range(rank, len(rows)) if rows[k][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][col]
        rows[rank] = [x/scale for x in rows[rank]]
        for k in range(len(rows)):
            if k != rank and rows[k][col]:
                scale = rows[k][col]
                rows[k] = [x-scale*y for x, y in zip(rows[k], rows[rank])]
        pivots.append(col)
        rank += 1
    assert rank == 11
    expected = [F(int(i == j)) for i in range(3) for j in range(3)]+[F(0)]*3
    assert all(sum(x*y for x, y in zip(row, expected)) == 0 for row in rows)
    return {'rotations': 24, 'affine_unknowns': 12, 'constraint_rank': rank,
            'solution_dimension': 12-rank, 'solution': 'A=lambda I3, t=0'}


def pauli(lam):
    assert -F(1, 3) <= lam <= 1
    return [(1+3*lam)/4]+[(1-lam)/4]*3


def compose(a, b):
    return [sum(a[i]*b[i ^ k] for i in range(4)) for k in range(4)]


def distance(a, b):
    return sum(abs(x-y) for x, y in zip(a, b))/2


def optimal_recovery(lam):
    mu = F(1) if lam >= 0 else -F(1, 3)
    return distance(compose(pauli(lam), pauli(mu)), pauli(F(1)))


def frontier(eps):
    assert 0 <= eps <= F(3, 4)
    return min(F(2, 3), F(3, 4)-eps)


def averaged_frontier(eps):
    assert 0 <= eps <= F(3, 4)
    return F(1, 2)-2*eps/3


def exact_checks():
    grid = [F(k, 36) for k in range(-12, 37)]
    compositions = 0
    for lam, mu in product(grid, repeat=2):
        a, b = pauli(lam), pauli(mu)
        assert min(a+b) >= 0 and sum(a) == sum(b) == 1
        assert compose(a, b) == pauli(lam*mu)
        error = distance(compose(a, b), pauli(F(1)))
        assert error == F(3, 4)*(1-lam*mu)
        assert error >= optimal_recovery(lam)
        compositions += 1
    rng = Random(20261024)
    ensembles = 0
    for keys in range(1, 8):
        for _ in range(128):
            raw = [rng.randrange(0, 20) for _ in range(keys)]
            if not sum(raw):
                raw[0] = 1
            weights = [F(x, sum(raw)) for x in raw]
            lambdas = [rng.choice(grid) for _ in range(keys)]
            mixture = [sum(w*pauli(lam)[i] for w, lam in zip(weights, lambdas)) for i in range(4)]
            avg = sum(w*lam for w, lam in zip(weights, lambdas))
            assert mixture == pauli(avg)
            eps = distance(mixture, pauli(F(0)))
            assert eps == F(3, 4)*abs(avg)
            delta = max(optimal_recovery(lam) for w, lam in zip(weights, lambdas) if w > 0)
            assert delta >= frontier(eps)
            restored = [[compose(pauli(lam), pauli(F(1) if lam >= 0 else -F(1, 3)))[i]
                         for i in range(4)] for lam in lambdas]
            average_restored = [sum(w*channel[i] for w, channel in zip(weights, restored))
                                for i in range(4)]
            average_error = distance(average_restored, pauli(F(1)))
            assert average_error == sum(w*optimal_recovery(lam) for w, lam in zip(weights, lambdas))
            assert average_error >= averaged_frontier(eps)
            ensembles += 1
    attained = 0
    for k in range(73):
        budget = F(k, 96)
        # Candidate A: two keys, identity and the universal-NOT channel.
        mixture = [F(1, 4)*x+F(3, 4)*y for x, y in zip(pauli(F(1)), pauli(-F(1, 3)))]
        assert mixture == pauli(F(0))
        delta_a = max(optimal_recovery(F(1)), optimal_recovery(-F(1, 3)))
        assert delta_a == F(2, 3)
        # Candidate B: one key and a depolarizing channel, decoded by identity.
        lam = 4*budget/3
        eps_b = distance(pauli(lam), pauli(F(0)))
        delta_b = distance(compose(pauli(lam), pauli(F(1))), pauli(F(1)))
        assert eps_b == budget
        assert min(delta_a, delta_b) == frontier(budget)
        # Average-channel recovery attains a different, linear frontier.
        w = (1+4*budget)/4
        ensemble = [w*x+(1-w)*y for x, y in zip(pauli(F(1)), pauli(-F(1, 3)))]
        assert distance(ensemble, pauli(F(0))) == budget
        recovered = [w*x+(1-w)*y for x, y in zip(pauli(F(1)), pauli(F(1, 9)))]
        assert distance(recovered, pauli(F(1))) == averaged_frontier(budget)
        attained += 1
    return {'Pauli_channel_composition_and_recovery_checks': compositions,
            'ensembles_checked': ensembles, 'key_counts': list(range(1, 8)),
            'attained_privacy_budget_settings': attained,
            'exact_privacy_two_key_recovery_error': '2/3',
            'privacy_budget_at_frontier_transition': '1/12'}


def main():
    result = {'covariance_commutant': commutant_check(),
              'exact_rational_checks': exact_checks(),
              'mathematical_frontier': 'For all-rotation-covariant qubit encoder branches, arbitrary qubit decoders, finitely many keys, privacy budget 0<=epsilon<=3/4, and maximum positive-key recovery error: delta_min = min(2/3, 3/4-epsilon). Two keys suffice to attain the frontier.',
              'averaged_recovery_channel_frontier': 'Half diamond distance of sum_k p_k decoder_k encoder_k from identity: delta_av_min = 1/2 - (2/3) epsilon. Two keys suffice.',
              'branch_covariance_required': True,
              'averaged_ciphertext_covariance_alone_is_sufficient': False,
              'arbitrary_quantum_decoders_covered_by_analytic_twirl_argument': True,
              'analytic_frontier_computer_verified': False,
              'reference_frame_resource_or_larger_ciphertext_covered': False,
              'higher_categorical_necessity_demonstrated': False,
              'Lean_checked': False, 'newness_established': False,
              'source_sha256': {str(Path(__file__).resolve()): hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
