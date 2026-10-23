"""Resource-filtered partial-response complexes for an n-of-n DL protocol.

Ranks are exact over F_2. Toy-group checks do not test DL hardness.
This certificate concerns homology, NOT necessity of an infinity-category.
"""

from itertools import combinations, product
from math import comb
from collections import Counter
from pathlib import Path
import hashlib
import json


def rank(columns):
    pivots = {}
    for column in columns:
        while column:
            pivot = column.bit_length() - 1
            if pivot in pivots:
                column ^= pivots[pivot]
            else:
                pivots[pivot] = column
                break
    return len(pivots)


def complex_data(n, budget):
    faces = [[tuple(f) for f in combinations(range(n), size)]
             for size in range(budget + 1)]
    boundary = []
    for size in range(1, budget + 1):
        index = {face: i for i, face in enumerate(faces[size - 1])}
        columns = [sum(1 << index[face[:j] + face[j + 1:]] for j in range(size))
                   for face in faces[size]]
        boundary.append(columns)
    for k in range(1, len(boundary)):
        for column in boundary[k]:
            twice = 0
            for j, previous in enumerate(boundary[k - 1]):
                if column >> j & 1:
                    twice ^= previous
            assert twice == 0
    ranks = [rank(columns) for columns in boundary]
    betti = [len(faces[d + 1]) - ranks[d]
             - (ranks[d + 1] if d + 1 < len(ranks) else 0)
             for d in range(budget)]
    assert betti == [0] * (budget - 1) + [comb(n - 1, budget)]
    return {"budget": budget, "reduced_betti_F2_by_degree": betti,
            "boundary_ranks_including_augmentation": ranks}


def protocol_fixture(n):
    p, q, g = 23, 11, 2
    for secret in range(q):
        known = [(3 * i + secret + 1) % q for i in range(n - 1)]
        shares = known + [(secret - sum(known)) % q]
        points = [pow(g, a, p) for a in shares]
        total = 1
        for point in points:
            total = total * point % p
        assert total == pow(g, secret, p)
        assert pow(g, sum(shares) % q, p) == total
        # The inverter programs one unknown share by group operations alone.
        y = pow(g, secret, p)
        for missing in range(n):
            factor = 1
            for i, value in enumerate(shares):
                if i != missing:
                    factor = factor * pow(g, value, p) % p
            assert y * pow(factor, -1, p) % p == points[missing]


def distribution_checks():
    checks = 0
    for n in (3, 4):
        for p, q, g in ((3, 2, 2), (7, 3, 2)):
            for secret in range(q):
                y = pow(g, secret, p)
                honest = Counter()
                for prefix in product(range(q), repeat=n - 1):
                    shares = prefix + ((secret - sum(prefix)) % q,)
                    honest[tuple(pow(g, a, p) for a in shares)] += 1
                for missing in range(n):
                    programmed = Counter()
                    for values in product(range(q), repeat=n - 1):
                        points = [None] * n
                        factor = 1
                        for i, scalar in zip([i for i in range(n) if i != missing], values):
                            points[i] = pow(g, scalar, p)
                            factor = factor * points[i] % p
                        points[missing] = y * pow(factor, -1, p) % p
                        programmed[tuple(points)] += 1
                    assert programmed == honest
                    checks += 1
    return checks


def main():
    records = []
    for n in range(3, 11):
        filtration = [complex_data(n, budget) for budget in range(1, n + 1)]
        assert filtration[-2]["reduced_betti_F2_by_degree"] == [0] * (n - 2) + [1]
        assert filtration[-1]["reduced_betti_F2_by_degree"] == [0] * n
        # Sum of all facets: every codimension-two face appears exactly twice.
        ridge_counts = Counter()
        for omitted in range(n):
            facet = tuple(i for i in range(n) if i != omitted)
            for j in range(n - 1):
                ridge_counts[facet[:j] + facet[j + 1:]] += 1
        assert len(ridge_counts) == comb(n, 2)
        assert set(ridge_counts.values()) == {2}
        protocol_fixture(n)
        records.append({"response_count": n, "cycle_degree": n - 2,
                        "cycle_birth_budget": n - 1, "cycle_death_budget": n,
                        "filtration": filtration,
                        "DL_reduction_loss": n,
                        "expected_query_lower": f"{n}*(1-delta-{n}*epsilon_DL)"})
    source = Path(__file__)
    print(json.dumps({
        "source_sha256": {source.as_posix(): hashlib.sha256(source.read_bytes()).hexdigest()},
        "lean_checked": False, "cryptographic_hardness_tested": False,
        "infinity_category_necessity_proved": False,
        "programmed_commitment_distribution_checks": distribution_checks(),
        "instances": records,
    }, indent=2))


if __name__ == "__main__":
    main()
