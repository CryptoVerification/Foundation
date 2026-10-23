"""Exact homology of access structures, with a bounded falsification search.

An observed correlation is not a theorem that Betti numbers determine cost.
Search domain: all nonempty cyclic unions of triple orbits on 8 or 9 labels.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
import hashlib
import importlib.util
import json
from pathlib import Path


HERE = Path(__file__).parent
RANK_SOURCE = HERE / "extraction-homology-filtration.py"
spec = importlib.util.spec_from_file_location("homology", RANK_SOURCE)
homology = importlib.util.module_from_spec(spec)
spec.loader.exec_module(homology)
N = 8


def rotate(s, shift, n=N):
    return sum(1 << ((i + shift) % n) for i in range(n) if s >> i & 1)


def analyze(edges, n=N):
    N = n
    wins = [any(s & e == e for e in edges) for s in range(1 << N)]
    faces = [[s for s in range(1 << N) if s.bit_count() == size and not wins[s]]
             for size in range(N + 1)]
    columns = []
    for size in range(1, N + 1):
        index = {s: i for i, s in enumerate(faces[size - 1])}
        columns.append([sum(1 << index[s ^ (1 << i)] for i in range(N) if s >> i & 1)
                        for s in faces[size]])
    for d in range(1, N):
        for column in columns[d]:
            twice = 0
            for i, previous in enumerate(columns[d - 1]):
                if column >> i & 1:
                    twice ^= previous
            assert twice == 0
    ranks = list(map(homology.rank, columns))
    betti = [len(faces[d + 1]) - ranks[d] - (ranks[d + 1] if d + 1 < N else 0)
             for d in range(N)]

    @lru_cache(None)
    def depth(s):
        if wins[s]:
            return 0
        useful = [c for c in range(N) if not s >> c & 1 and any(
            e >> c & 1 and not wins[s | (e & ~(1 << c))] for e in edges)]
        assert useful
        return 1 + max(depth(s | 1 << c) for c in useful)

    @lru_cache(None)
    def value(s):
        if wins[s]:
            return Q(0)
        r = N - s.bit_count()
        return min(Q(1) + Q(r - 1, r) * value(s | 1 << c)
                   + Q(1, r) * min((e & ~s).bit_count() for e in edges if not e >> c & 1)
                   for c in range(N) if not s >> c & 1)

    return {
        "minimal_triple_masks": sorted(edges),
        "face_counts_including_empty": list(map(len, faces)),
        "boundary_ranks_including_augmentation": ranks,
        "reduced_betti_F2_by_degree": betti,
        "kappa": str(Q(max(s.bit_count() for s in range(1 << N) if not wins[s]), N)),
        "useful_extension_depth": depth(0), "expected_queries": str(value(0)),
    }


def collision(rows, key):
    groups = {}
    for row in rows:
        k = key(row)
        old = groups.setdefault(k, row)
        if old["expected_queries"] != row["expected_queries"]:
            return {"first": old, "second": row}
    return None


def search(n):
    triples = {sum(1 << i for i in t) for t in combinations(range(n), 3)}
    orbits = []
    while triples:
        seed = min(triples)
        orbit = {rotate(seed, shift, n) for shift in range(n)}
        orbits.append(orbit)
        triples -= orbit
    rows = [analyze(set().union(*(o for j, o in enumerate(orbits) if choice >> j & 1)), n)
            for choice in range(1, 1 << len(orbits))]
    return {
        "challenge_count": n, "cyclic_families_searched": len(rows),
        "same_kappa_depth_beta2_but_different_cost": collision(
            rows, lambda r: (r["kappa"], r["useful_extension_depth"], r["reduced_betti_F2_by_degree"][2])),
        "same_kappa_depth_all_betti_but_different_cost": collision(
            rows, lambda r: (r["kappa"], r["useful_extension_depth"], tuple(r["reduced_betti_F2_by_degree"]))),
    }


def main():
    searches = [search(n) for n in (8, 9)]
    assert [s["cyclic_families_searched"] for s in searches] == [127, 1023]
    b = analyze({rotate(11, shift) for shift in range(N)})
    c = analyze({rotate(19, shift) for shift in range(N)})
    assert b["reduced_betti_F2_by_degree"] == [0, 0, 1, 4, 0, 0, 0, 0]
    assert c["reduced_betti_F2_by_degree"] == [0, 0, 0, 7, 0, 0, 0, 0]
    assert b["expected_queries"] == "7/2" and c["expected_queries"] == "27/8"
    sources = (Path(__file__), RANK_SOURCE)
    print(json.dumps({
        "source_sha256": {s.as_posix(): hashlib.sha256(s.read_bytes()).hexdigest() for s in sources},
        "lean_checked": False, "infinity_category_necessity_proved": False,
        "coefficient_field": "F_2",
        "B": b, "C": c,
        "searches": searches,
    }, indent=2))


if __name__ == "__main__":
    main()
