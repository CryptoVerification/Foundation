"""Exact integer filling and cache-accounting checks for the fan model.

This checks an execution-to-chain map, not a DL security assumption. The Lean
module proves the general certificate, exact fan mass, and trace bound.
"""

from itertools import product
import hashlib
import json
from pathlib import Path


LEAN = Path("Foundation/Examples/IntegralFillingExtraction.lean")


def boundary(chain):
    n = len(chain)
    return tuple(chain), tuple(chain[i] - chain[(i - 1) % n] for i in range(n))


def target(n, k=1):
    return (k,) * n, (0,) * n


def mass(chain, weights):
    return sum(w * abs(c) for w, c in zip(weights, chain))


def main():
    signed_checks = 0
    trace_checks = 0
    records = []
    for n in range(3, 7):
        weights = tuple(1 + i % 3 for i in range(n))
        for chain in product(range(-2, 3), repeat=n):
            outer, radial = boundary(chain)
            # A genuine dual lower-bound certificate, valid with signs.
            potential = sum(w * c for w, c in zip(weights, outer))
            assert abs(potential) <= mass(chain, weights)
            for k in range(-2, 3):
                if (outer, radial) == target(n, k):
                    assert chain == (k,) * n
                    assert mass(chain, weights) == abs(k) * sum(weights)
            signed_checks += 1
        if n <= 5:
            for length in range(7):
                for events in product((None, *range(n)), repeat=length):
                    accepted = [i for i in events if i is not None]
                    seen = set(accepted)
                    chain = tuple(int(i in seen) for i in range(n))
                    assert mass(chain, (1,) * n) == len(seen)
                    assert len(seen) <= len(accepted) <= len(events)
                    assert (boundary(chain) == target(n)) == (len(seen) == n)
                    assert mass(chain, weights) <= sum(weights[i] for i in accepted)
                    if boundary(chain) == target(n):
                        assert n <= len(events)
                    # Re-reading an already cached label leaves the chain alone.
                    for cached in seen:
                        assert tuple(int(i in seen | {cached}) for i in range(n)) == chain
                    trace_checks += 1
        records.append({
            "labels": n, "cell_weights": list(weights),
            "exact_unit_target_integral_filling_mass": n,
            "exact_weighted_target_filling_mass": sum(weights),
            "double_target_integral_mass": 2 * n,
            "double_target_mod_two": "zero",
        })
    source = Path(__file__)
    print(json.dumps({
        "source_sha256": {p.as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (source, LEAN)},
        "signed_chains_checked": signed_checks,
        "traces_with_rejections_and_repetitions_checked": trace_checks,
        "cryptographic_hardness_tested": False,
        "cryptographic_success_not_identified_with_collection": True,
        "instances": records,
        "limitation": "Linear fan example; no strict integral-versus-real gap or infinity-category necessity.",
    }, indent=2))


if __name__ == "__main__":
    main()
