"""Equal-size shares and error-robust bounds; no cryptographic hardness test.

The discrete-log assumption and the reduction are mathematical statements in
docs/polygraphic-security.md. This script verifies only their finite access
structures, policies, sharing marginals, and numerical bound arithmetic.
"""

from fractions import Fraction as Q
from itertools import combinations, product
import hashlib
import importlib.util
import json
from pathlib import Path


BASE = Path(__file__).with_name("extraction-query-minimax.py")
spec = importlib.util.spec_from_file_location("query_minimax", BASE)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def marginal(secret, q, observed):
    counts = {}
    for r, t in product(range(q), repeat=2):
        shares = (r, t, (secret - r - t) % q)
        view = tuple(shares[i] for i in observed)
        counts[view] = counts.get(view, 0) + 1
    return counts


def main():
    c, b = base.analyze([19]), base.analyze([11])
    assert c["kappa"] == b["kappa"] == "1/2"
    assert c["useful_extension_depth"] == b["useful_extension_depth"] == 5
    assert c["share_bits_per_participant_for_one_secret_bit"] == [3] * 8
    assert b["share_bits_per_participant_for_one_secret_bit"] == [3] * 8
    assert len(c["minimal_accepted_triples"]) == len(b["minimal_accepted_triples"]) == 8
    assert c["minimax_expected_response_queries"] == "27/8"
    assert b["minimax_expected_response_queries"] == "7/2"
    assert max(c["optimal_cost_by_rejecting_label"]) == 4
    assert max(b["optimal_cost_by_rejecting_label"]) == 5

    checks = 0
    for q in (2, 3, 5):
        for size in range(3):
            for observed in combinations(range(3), size):
                reference = marginal(0, q, observed)
                for secret in range(q):
                    assert marginal(secret, q, observed) == reference
                    checks += 1
        for secret, r, t in product(range(q), repeat=3):
            assert (r + t + (secret - r - t)) % q == secret

    # Illustrative arithmetic only. No claim that these are measured security
    # bounds of an instantiated group or of a concrete inverter.
    delta, epsilon = Q(1, 100), Q(1, 1000)
    lower = Q(7, 2) - 5 * (delta + epsilon)
    assert lower > Q(27, 8)
    assert Q(7, 2) - 5 * Q(1, 40) == Q(27, 8)
    paths = (Path(__file__), BASE)
    print(json.dumps({
        "source_sha256": {p.as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        "lean_checked": False,
        "cryptographic_hardness_tested": False,
        "C_equal_payload": c, "B": b,
        "additive_sharing_marginal_checks": checks,
        "field_orders_tested": [2, 3, 5],
        "bounded_error_information_theoretic_B_lower": "7/2 - 5*delta/(1 - 1/q)",
        "public_discrete_log_B_lower": "7/2 - 5*(delta + epsilon_DL)",
        "strict_query_separation_condition": "delta + epsilon_DL < 1/40",
        "illustrative_arithmetic_only": {
            "delta": str(delta), "epsilon_DL": str(epsilon),
            "B_lower": str(lower), "C_zero_error_upper": "27/8",
        },
    }, indent=2))


if __name__ == "__main__":
    main()
