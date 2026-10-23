"""Exact query bounds for collecting an accepted access-structure basis.

One of eight labels rejects. Every response query costs one, including the
first query and rejecting queries. The collector must succeed with zero error.
This is NOT a lower bound for unrestricted cryptographic witness extractors.
Run from the repository root; stdout is the reproducible JSON certificate.
"""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, permutations
import hashlib
import json
from pathlib import Path


N = 8
FULL = (1 << N) - 1


def rotate(mask, shift):
    return sum(1 << ((i + shift) % N) for i in range(N) if mask >> i & 1)


def labels(mask):
    return [i for i in range(N) if mask >> i & 1]


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return len(pivots)


def analyze(seeds):
    edges = sorted({rotate(seed, shift) for seed in seeds for shift in range(N)})

    def winning(s):
        return any(s & e == e for e in edges)

    # Explicit perfect sharing: for each triple e independently choose two
    # uniform bits r_e,t_e, and distribute r_e,t_e,secret XOR r_e XOR t_e.
    # The same secret is used across edges. Rank tests verify that precisely
    # the authorized subsets determine it; all other subsets hide it perfectly.
    shares = [[] for _ in range(N)]
    for j, e in enumerate(edges):
        a, b, c = labels(e)
        r, t = 1 << (2 * j + 1), 1 << (2 * j + 2)
        shares[a].append(r)
        shares[b].append(t)
        shares[c].append(1 ^ r ^ t)
    for s in range(1 << N):
        rows = [row for i in labels(s) for row in shares[i]]
        assert (binary_rank(rows + [1]) == binary_rank(rows)) == winning(s)

    def completion(s, bad):
        return min(((e & ~s).bit_count(), e) for e in edges if not e >> bad & 1)

    def actions(s):
        left = N - s.bit_count()
        return {
            c: Q(1) + Q(left - 1, left) * value(s | (1 << c))
            + Q(1, left) * completion(s, c)[0]
            for c in range(N) if not s >> c & 1
        }

    @lru_cache(None)
    def value(s):
        return Q(0) if winning(s) else min(actions(s).values())

    @lru_cache(None)
    def depth(s):
        if winning(s):
            return 0
        useful = [c for c in range(N) if not s >> c & 1 and any(
            e >> c & 1 and not winning(s | (e & ~(1 << c))) for e in edges)]
        assert useful
        return 1 + max(depth(s | (1 << c)) for c in useful)

    states = []
    checks = 0
    for s in range(1 << N):
        v = value(s)
        if winning(s):
            assert v == 0
            continue
        costs = actions(s)
        assert all(v <= cost for cost in costs.values())
        assert any(v == cost for cost in costs.values())
        for c in costs:
            k, e = completion(s, c)
            assert not e >> c & 1
            assert winning(s | e)
            # Independently enumerate every possible completion set.
            available = FULL & ~s & ~(1 << c)
            assert k == min(t.bit_count() for t in range(1 << N)
                            if t & ~available == 0 and winning(s | t))
            checks += 1
        states.append({"accepted_mask": s, "potential": str(v),
                       "action_costs": {str(c): str(x) for c, x in costs.items()}})

    # Independent exhaustive check. Before its first rejection any deterministic
    # policy follows one ordered all-accept path. After rejection it knows the
    # entire remaining accept/reject pattern, so cheapest completion is optimal.
    totals = Counter()
    best = None
    for order in permutations(range(N)):
        s = 0
        rejection_costs = {}
        for step, c in enumerate(order, 1):
            rejection_costs[c] = step + completion(s, c)[0]
            s |= 1 << c
            if winning(s):
                costs = [rejection_costs.get(b, step) for b in range(N)]
                break
        total = sum(costs)
        totals[total] += 1
        if best is None or total < best[0]:
            best = (total, list(order[:step]), costs)
    assert sum(totals.values()) == 40320
    assert Q(best[0], N) == value(0)

    # Rotating a fixed optimal policy uniformly makes its expectation equal
    # across every fixed hidden rejecting label, proving minimax attainability.
    rotated = [sum((Q(best[2][(bad - shift) % N], N)
                    for shift in range(N)), Q(0)) for bad in range(N)]
    assert rotated == [value(0)] * N
    assert all(rotate(e, 1) in edges for e in edges)
    assert all(not winning(sum(1 << i for i in pair))
               for pair in combinations(range(N), 2))
    kappa = Q(max(s.bit_count() for s in range(1 << N) if not winning(s)), N)
    return {
        "minimal_accepted_triples": [labels(e) for e in edges],
        "secret_sharing_rank_checks": 1 << N,
        "share_bits_per_participant_for_one_secret_bit": list(map(len, shares)),
        "maximum_number_of_triples_containing_a_pair": max(
            sum(e & pair == pair for e in edges)
            for pair in (sum(1 << i for i in p) for p in combinations(range(N), 2))),
        "kappa": str(kappa), "useful_extension_depth": depth(0),
        "minimax_expected_response_queries": str(value(0)),
        "optimal_all_accept_prefix": best[1],
        "optimal_cost_by_rejecting_label": best[2],
        "rotation_averaged_cost_by_rejecting_label": list(map(str, rotated)),
        "permutation_total_cost_histogram": dict(sorted(totals.items())),
        "bellman_action_checks": checks, "losing_state_certificate": states,
    }


def main():
    a, b = analyze([7, 11]), analyze([11])
    assert (a["kappa"], a["useful_extension_depth"]) == ("1/2", 5)
    assert (b["kappa"], b["useful_extension_depth"]) == ("1/2", 5)
    assert a["minimax_expected_response_queries"] == "27/8"
    assert b["minimax_expected_response_queries"] == "7/2"
    source = Path(__file__)
    print(json.dumps({
        "model": "zero-error accepted-basis collection; one hidden rejecting label",
        "challenge_count": N, "acceptance_probability": "7/8",
        "cost_unit": "one response query; first and rejecting queries counted",
        "cryptographic_extractor_lower_bound": False,
        "lean_checked": False,
        "source_sha256": {source.as_posix(): hashlib.sha256(source.read_bytes()).hexdigest()},
        "A": a, "B": b,
    }, indent=2))


if __name__ == "__main__":
    main()
