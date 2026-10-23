"""Exact, scope-qualified research checks for crossing rewinding.

The compiler handles a fixed guessing policy: all commitments first, then
responses in the same order, resetting to the failed session's commitment.
It proves costs, not zero-knowledge. A separate exact counterexample shows why
normalizing each continuation separately does not ensure the correct output law.
"""

from fractions import Fraction as F
from itertools import combinations, product
import hashlib
import json
from pathlib import Path


LEAN = Path("Foundation/Examples/CrossingRewindingCost.lean")


def solve(matrix, target):
    rows = [[F(v) for v in row] + [F(t)] for row, t in zip(matrix, target)]
    nr, nc = len(rows), len(matrix[0])
    rank, pivots = 0, []
    for col in range(nc):
        pivot = next((i for i in range(rank, nr) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][col]
        rows[rank] = [v / scale for v in rows[rank]]
        for i in range(nr):
            if i != rank and rows[i][col]:
                scale = rows[i][col]
                rows[i] = [a - scale * b for a, b in zip(rows[i], rows[rank])]
        pivots.append(col)
        rank += 1
        if rank == nr:
            break
    if any(not any(row[:-1]) and row[-1] for row in rows):
        return None
    answer = [F(0)] * nc
    for i, col in enumerate(pivots):
        answer[col] = rows[i][-1]
    assert all(sum(a * x for a, x in zip(row, answer)) == t
               for row, t in zip(matrix, target))
    return answer


def prefixes(cuts):
    """Construct the invariant family directly from syntax, without histories."""
    n = len(cuts)
    states = {(1 << n) - 1}
    for j in range(n):
        reset = sum(1 << i for i in range(n) if cuts[i] < j)
        for p in range(j + 1):
            states.add(reset | ((1 << p) - 1))
    assert len(states) <= n * (n + 1) // 2 + 1
    return sorted(states)


def transition(cuts, state):
    n = len(cuts)
    i = next(i for i in range(n) if not (state >> i & 1))
    reset = sum(1 << k for k in range(n) if cuts[k] < i)
    mask = sum(1 << k for k in range(n) if cuts[k] >= i)
    # This equality depends on the first-missing policy and cuts[k] >= k.
    assert state & ~mask == reset
    return i, state | (1 << i), reset


def monomials(n, degree):
    return [sum(1 << i for i in indices)
            for k in range(degree + 1) for indices in combinations(range(n), k)]


def compile_certificate(cuts):
    n, goal = len(cuts), (1 << len(cuts)) - 1
    assert all(i <= cut < n for i, cut in enumerate(cuts))
    states = prefixes(cuts)
    active = [s for s in states if s != goal]
    index = {s: i for i, s in enumerate(active)}
    matrix = []
    for s in active:
        _, passed, failed = transition(cuts, s)
        assert passed in states and failed in states
        row = [F(0)] * len(active)
        row[index[s]] = 1
        for target in (passed, failed):
            if target != goal:
                row[index[target]] -= F(1, 2)
        matrix.append(row)
    remaining_list = solve(matrix, [F(1)] * len(active))
    assert remaining_list is not None
    remaining = dict(zip(active, remaining_list))
    remaining[goal] = F(0)
    initial_cost = remaining[0]
    target_values = [initial_cost - remaining[s] for s in states]
    basis = monomials(n, 2)
    evaluation = [[int(s & m == m) for m in basis] for s in states]
    quadratic = solve(evaluation, target_values)
    assert quadratic is not None
    phi = {s: sum(c for m, c in zip(basis, quadratic) if s & m == m)
           for s in states}
    assert phi[0] == 0 and phi[goal] == initial_cost
    for s in active:
        _, passed, failed = transition(cuts, s)
        assert (phi[passed] + phi[failed]) / 2 - phi[s] == 1
    linear_basis = monomials(n, 1)
    linear = solve([[int(s & m == m) for m in linear_basis] for s in states],
                   target_values)
    # Verify all triple coverage identities used by the general degree proof.
    for triple in combinations(range(n), 3):
        first_min = min(triple)
        scope_min = min(triple, key=lambda i: (cuts[i], i))
        middle = next(i for i in triple if i not in {first_min, scope_min})
        for s in states:
            x, a, b = (int(s >> i & 1) for i in (middle, first_min, scope_min))
            assert x * (1 - a) * (1 - b) == 0
    return {
        "cuts": list(cuts), "invariant_states": states,
        "exact_expected_fresh_challenge_checks": str(initial_cost),
        "affine_exact": linear is not None,
        "quadratic_coefficients": {str(m): str(c) for m, c in zip(basis, quadratic) if c},
        "remaining_costs": {str(s): str(remaining[s]) for s in states},
    }


def concrete_trace_checks():
    """Independently compare symbolic flags with actual prefix-key caches.

    Public unique tags are part of this tagged Schnorr checking example. The
    strategy prepares only challenge-zero responses. No ZK-law claim is made.
    """
    streams, transitions = 0, 0
    modulus, generator, public = 23, 2, pow(2, 7, 23)
    for n in range(1, 4):
        for cuts in product(*(range(i, n) for i in range(n))):
            allowed = set(prefixes(cuts))
            for budget in range(9):
                for outcomes in product((0, 1), repeat=budget):
                    next_tag = 0
                    commitments = []
                    table = {}

                    def replace_from(j):
                        nonlocal next_tag
                        del commitments[j:]
                        for _ in range(j, n):
                            next_tag += 1
                            z = next_tag % 11
                            commitments.append((next_tag, pow(generator, z, modulus), z))

                    def key(i):
                        return i, tuple((t, a) for t, a, _ in commitments[:cuts[i] + 1])

                    def valid_flags():
                        return sum(1 << i for i in range(n) if table.get(key(i)) == 0)

                    replace_from(0)
                    flags = 0
                    for coin in outcomes:
                        assert flags == valid_flags() and flags in allowed
                        if flags == (1 << n) - 1:
                            break
                        i, passed, failed = transition(cuts, flags)
                        challenge_key = key(i)
                        assert challenge_key not in table
                        table[challenge_key] = coin
                        if coin == 0:
                            _, a, z = commitments[i]
                            assert pow(generator, z, modulus) == a * pow(public, 0, modulus) % modulus
                            flags = passed
                        else:
                            replace_from(i)
                            flags = failed
                        assert flags == valid_flags()
                        transitions += 1
                    streams += 1
    return streams, transitions


def exit_kernel(tag_a, guess_a):
    """A real tagged Schnorr verifier has c_A=0 if tag_A=0 else tag_B,
    and c_B=0. All group commitments are uniform and independent of guesses.
    Return an unnormalized successful output kernel and the cost of an outer
    attempt, allowing B-only retries but ending at an A retry.
    """
    loop, checks = F(0), F(0)
    exits = {0: F(0), 1: F(0)}
    for tag_b, guess_b in product((0, 1), repeat=2):
        challenge_a = 0 if tag_a == 0 else tag_b
        matches_a = guess_a == challenge_a
        checks += F(1 + matches_a, 4)
        if matches_a and guess_b != 0:
            loop += F(1, 4)
        if matches_a and guess_b == 0:
            exits[tag_b] += F(1, 4)
    return {t: p / (1 - loop) for t, p in exits.items()}, checks / (1 - loop)


def law_and_cost(proposal_tag_zero):
    mass = {(a, b): F(0) for a, b in product((0, 1), repeat=2)}
    cost = F(0)
    for tag_a, guess_a in product((0, 1), repeat=2):
        proposal = (proposal_tag_zero if tag_a == 0 else 1 - proposal_tag_zero) / 2
        kernel, local_cost = exit_kernel(tag_a, guess_a)
        cost += proposal * local_cost
        for tag_b, probability in kernel.items():
            mass[tag_a, tag_b] += proposal * probability
    normalizer = sum(mass.values())
    law = {key: value / normalizer for key, value in mass.items()}
    return law, cost / normalizer


def distribution_checks():
    biased, biased_cost = law_and_cost(F(1, 2))
    repaired, repaired_cost = law_and_cost(F(2, 5))
    assert sum(p for (a, _), p in biased.items() if a == 0) == F(3, 5)
    assert sum(abs(p - F(1, 4)) for p in biased.values()) / 2 == F(1, 10)
    assert biased_cost == F(27, 5)
    assert set(repaired.values()) == {F(1, 4)}
    assert repaired_cost == F(11, 2)
    # Check actual Schnorr preparation identities on every group exponent,
    # guess and public witness in the small test group.
    checks = 0
    for secret, z, guess in product(range(11), range(11), (0, 1)):
        public = pow(2, secret, 23)
        commitment = pow(2, (z - guess * secret) % 11, 23)
        assert pow(2, z, 23) == commitment * pow(public, guess, 23) % 23
        checks += 1
    return {
        "greedy_tag_law": {str(k): str(v) for k, v in biased.items()},
        "greedy_expected_challenge_checks": str(biased_cost),
        "greedy_total_variation_from_honest_joint_tag_law": "1/10",
        "full_restart_expected_challenge_checks": "6",
        "reweighted_proposal_tag_zero_probability": "2/5",
        "reweighted_tag_law": {str(k): str(v) for k, v in repaired.items()},
        "reweighted_expected_challenge_checks": str(repaired_cost),
        "Schnorr_preparation_identities_checked": checks,
        "optimal_over_all_simulators": False,
        "generic_black_box_ZK_simulation_theorem": False,
    }


def main():
    records = []
    for n in range(1, 7):
        for cuts in product(*(range(i, n) for i in range(n))):
            records.append(compile_certificate(cuts))
    example = compile_certificate((2, 1, 2))
    assert example["exact_expected_fresh_challenge_checks"] == "12"
    assert not example["affine_exact"]
    assert example["quadratic_coefficients"] == {"1": "2", "2": "2", "4": "6", "3": "2"}
    streams, transitions = concrete_trace_checks()
    result = {
        "scope": "fixed FIFO reset policy, prefix-scoped private challenges, explicit freshness",
        "exhaustive_scope_vectors_by_session_count": {str(n): sum(len(r["cuts"]) == n for r in records)
                                                     for n in range(1, 7)},
        "scope_vectors_checked": len(records),
        "models_requiring_quadratic_terms_for_exactness": sum(not r["affine_exact"] for r in records),
        "max_invariant_family_size": max(len(r["invariant_states"]) for r in records),
        "three_session_example": example,
        "tagged_Schnorr_coin_streams_checked": streams,
        "tagged_Schnorr_cache_quotient_transitions_checked": transitions,
        "distribution_counterexample_and_repair": distribution_checks(),
        "source_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__), LEAN)},
        "general_compiler_Lean_checked": False,
        "arbitrary_crypto_simulator_optimality_proved": False,
        "newness_established": False,
        "infinity_category_necessity_proved": False,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
