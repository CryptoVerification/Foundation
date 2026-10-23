"""Exact rational certificate for the four-context feasibility test.

The optimum is for a context-independent common four-bit output, measured by
the largest total variation error among its four three-bit marginals. This is
not a black-box cryptographic reduction separation or an H^2 computation.
"""

from fractions import Fraction as Q
from itertools import combinations, product
import json


TRIPLES = tuple(product((0, 1), repeat=3))
QUADS = tuple(product((0, 1), repeat=4))
FACES = range(4)


def drop(x, face):
    return x[:face] + x[face + 1 :]


def target(t):
    return Q(1, 4) if sum(t) % 2 == 0 else Q(0)


def score(t):
    return (0, -1, 1, -3)[sum(t)]


def marginal(weights, face):
    return {t: sum((p for x, p in weights.items() if drop(x, face) == t), Q(0)) for t in TRIPLES}


def total_variation(left, right):
    return sum((abs(left[t] - right[t]) for t in TRIPLES), Q(0)) / 2


def main():
    desired = {t: target(t) for t in TRIPLES}
    assert sum(desired.values()) == 1
    for coords in combinations(range(3), 2):
        for pair in product((0, 1), repeat=2):
            assert sum(p for t, p in desired.items() if tuple(t[c] for c in coords) == pair) == Q(1, 4)

    certificate = {''.join(map(str, x)): sum(score(drop(x, f)) for f in FACES) for x in QUADS}
    assert max(certificate.values()) == 0
    target_expectation = sum(target(t) * score(t) for t in TRIPLES)
    assert target_expectation == Q(3, 4)
    assert max(score(t) for t in TRIPLES) - min(score(t) for t in TRIPLES) == 4

    # For ANY nonnegative normalized global law q, linearity and the pointwise
    # certificate give sum_f E[q_f, score] <= 0. Hence
    # 3 <= sum_f (E[target, score] - E[q_f, score]) <= 4 sum_f TV(target,q_f)
    # <= 16 max_f TV(target,q_f). This proves the universal lower bound 3/16;
    # no grid search or numerical optimization over global laws is used.
    optimum = Q(3, 16)
    achieving = {x: Q(1, 4) if sum(x) == 0 else Q(3, 16) if sum(x) == 3 else Q(0) for x in QUADS}
    assert sum(achieving.values()) == 1
    errors = [total_variation(marginal(achieving, f), desired) for f in FACES]
    assert errors == [optimum] * 4

    # Escape control: when the context is known before producing the shares,
    # two fair bits generate the required law exactly. The impossibility is
    # therefore not a statement about every randomized contextual simulator.
    generated = {t: Q(0) for t in TRIPLES}
    for a, b in product((0, 1), repeat=2):
        generated[(a, b, a ^ b)] += Q(1, 4)
    assert generated == desired

    # Uniformly choose one of the four contexts after the global output is
    # fixed, then accept with probability (score(triple)+3)/4. This is a
    # concrete single test for all context-independent simulators.
    accept = {t: Q(score(t) + 3, 4) for t in TRIPLES}
    assert all(0 <= a <= 1 for a in accept.values())
    ideal_acceptance = sum(desired[t] * accept[t] for t in TRIPLES)
    global_acceptance_upper = Q(3, 4)
    assert ideal_acceptance == Q(15, 16)
    assert ideal_acceptance - global_acceptance_upper == optimum
    for x in QUADS:
        assert sum(accept[drop(x, f)] for f in FACES) / 4 <= global_acceptance_upper

    # A support-only test also has a globally compatible assignment. Thus the
    # example is not strong contextuality; nonnegative probabilities matter.
    assert all(target(drop((0, 0, 0, 0), f)) > 0 for f in FACES)
    print(json.dumps({
        'global_assignments_checked': len(QUADS),
        'local_assignments_per_context': len(TRIPLES),
        'contexts': 4,
        'all_pair_marginals': 'uniform 1/4',
        'target_score_per_context': str(target_expectation),
        'global_score_certificate': certificate,
        'minimum_worst_context_total_variation': str(optimum),
        'achieving_joint': {''.join(map(str, x)): str(p) for x, p in achieving.items() if p},
        'achieving_errors': [str(e) for e in errors],
        'context_aware_escape': 'exact sampler from two fair bits',
        'single_test_ideal_acceptance': str(ideal_acceptance),
        'single_test_global_acceptance_upper': str(global_acceptance_upper),
        'single_test_distinguishing_gap_lower': str(optimum),
        'support_only_global_assignment_exists': True,
        'higher_cohomology_class_computed': False,
        'cryptographic_reduction_bridge_proved': False,
    }, indent=2))


if __name__ == '__main__':
    main()
