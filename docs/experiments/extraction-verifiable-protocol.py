"""Reference three-message DL knowledge protocol and finite consistency checks.

Toy groups here have trivial discrete logarithms. These tests establish finite
identities/distribution equalities, NOT cryptographic security or Lean proofs.
The fixed-first-message extraction lower bound is proved in the research note.
"""

from collections import Counter
from fractions import Fraction as Q
import hashlib
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path


BASE = Path(__file__).with_name("extraction-query-minimax.py")
spec = importlib.util.spec_from_file_location("query_minimax", BASE)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def first_valid(packet, y, p, q):
    return all(len(row) == 3 and all(0 < a < p and pow(a, q, p) == 1 for a in row)
               and row[0] * row[1] * row[2] % p == y for row in packet)


def verify(edges, packet, challenge, response, y, p, q, g):
    if len(packet) != len(edges) or not first_valid(packet, y, p, q):
        return False
    wanted = {(j, edge.index(challenge)) for j, edge in enumerate(edges) if challenge in edge}
    if set(response) != wanted:
        return False
    return all(0 <= scalar < q and pow(g, scalar, p) == packet[j][k]
               for (j, k), scalar in response.items())


def response_for(edges, shares, challenge):
    return {(j, edge.index(challenge)): shares[j][edge.index(challenge)]
            for j, edge in enumerate(edges) if challenge in edge}


def programmed_row(y, missing, known, p, g):
    """Does not take or compute log_g(y)."""
    points = [None] * 3
    for i, scalar in known.items():
        points[i] = pow(g, scalar, p)
    factor = 1
    for i in range(3):
        if i != missing:
            factor = factor * points[i] % p
    points[missing] = y * pow(factor, -1, p) % p
    return tuple(points)


def view(points, scalars, observed):
    return points, tuple(scalars[i] for i in observed)


def main():
    summary = {}
    for name, seed, expected_maximal in (("C", 19, 34), ("B", 11, 30)):
        info = base.analyze([seed])
        edges = [tuple(e) for e in info["minimal_accepted_triples"]]
        masks = [sum(1 << i for i in e) for e in edges]
        winning = lambda s: any(s & e == e for e in masks)
        losing = [s for s in range(256) if not winning(s)]
        maximal = [s for s in losing if all(winning(s | 1 << i)
                   for i in range(8) if not s >> i & 1)]
        assert len(maximal) == expected_maximal
        assert all(any(s & m == s for m in maximal) for s in losing)
        assert all(s.bit_count() <= 4 for s in losing)
        assert all(len([e for e in edges if i in e]) == 3 for i in range(8))

        # Every losing set is covered by at least one uniformly guessed maximal
        # losing set; every edge has an unobserved coordinate to hold y.
        for m in maximal:
            assert all(any(not m >> i & 1 for i in e) for e in edges)
        survival = min(Q(sum(s & m == s for m in maximal), len(maximal)) for s in losing)
        assert survival == Q(1, expected_maximal)

        protocol_checks = 0
        for p, q, g in ((7, 3, 2), (11, 5, 3), (23, 11, 2)):
            assert pow(g, q, p) == 1 and g != 1
            for secret in range(q):
                y = pow(g, secret, p)
                shares = [((j + secret) % q, (2 * j + 1) % q,
                           (secret - (j + secret) - (2 * j + 1)) % q)
                          for j in range(len(edges))]
                packet = [tuple(pow(g, a, p) for a in row) for row in shares]
                assert first_valid(packet, y, p, q)
                responses = [response_for(edges, shares, i) for i in range(8)]
                assert all(verify(edges, packet, i, responses[i], y, p, q, g) for i in range(8))
                for j, edge in enumerate(edges):
                    witness = sum(responses[i][(j, edge.index(i))] for i in edge) % q
                    assert pow(g, witness, p) == y
                altered = [tuple(row) for row in packet]
                altered[0] = (altered[0][0] * g % p,) + altered[0][1:]
                assert not first_valid(altered, y, p, q)
                bad_response = dict(responses[0])
                key = next(iter(bad_response))
                bad_response[key] = (bad_response[key] + 1) % q
                assert not verify(edges, packet, 0, bad_response, y, p, q, g)
                protocol_checks += 1
        summary[name] = {
            "maximal_nonextractable_set_count": len(maximal),
            "minimal_guess_survival_probability": str(survival),
            "maximal_nonextractable_sets": [base.labels(m) for m in maximal],
            "protocol_fixture_checks": protocol_checks,
            "first_message_group_elements": 24, "response_field_elements": 3,
            "lower_bound": ("27/8 - 4*(delta + 34*epsilon_DL)" if name == "C"
                            else "7/2 - 5*(delta + 30*epsilon_DL)"),
        }

    # Exact distribution equality for each edge: even its public exponent
    # commitments do not reveal which coordinate contains the unknown DL.
    distribution_checks = 0
    for p, q, g in ((3, 2, 2), (7, 3, 2), (11, 5, 3)):
        for secret in range(q):
            y = pow(g, secret, p)
            for size in range(3):
                for observed in combinations(range(3), size):
                    honest = Counter()
                    for r, t in product(range(q), repeat=2):
                        scalars = (r, t, (secret - r - t) % q)
                        points = tuple(pow(g, a, p) for a in scalars)
                        honest[view(points, scalars, observed)] += 1
                    for missing in range(3):
                        if missing in observed:
                            continue
                        programmed = Counter()
                        known_indices = [i for i in range(3) if i != missing]
                        for values in product(range(q), repeat=2):
                            known = dict(zip(known_indices, values))
                            points = programmed_row(y, missing, known, p, g)
                            programmed[view(points, known, observed)] += 1
                        assert programmed == honest
                        distribution_checks += 1

    assert Q(7, 2) - 5 * Q(1, 40) == Q(27, 8)
    sources = (Path(__file__), BASE)
    print(json.dumps({
        "source_sha256": {s.as_posix(): hashlib.sha256(s.read_bytes()).hexdigest() for s in sources},
        "lean_checked": False, "cryptographic_hardness_tested": False,
        "model": "classical black-box extraction at one fixed first message and random tape",
        "distribution_equality_checks": distribution_checks,
        "knowledge_extraction_success_with_eight_queries": "at least max(0,2*acceptance-1)",
        "strict_separation_condition": "delta + 30*epsilon_DL < 1/40",
        **summary,
    }, indent=2))


if __name__ == "__main__":
    main()
