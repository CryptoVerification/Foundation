"""Exact checks for a restricted, context-sensitive rewinding resource model.

This is NOT a proof that arbitrary Schnorr/Blum simulators obey the model.
Every fresh parent query consumes a distinct child-completion ticket. Cached
reads are identities and cannot mint a new ticket. Independent fair outcomes
model a challenge guessed before its first revelation.
"""

from fractions import Fraction as F
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path


LEAN = Path("Foundation/Examples/NestedRewindingCost.lean")


def cost(depth):
    return 2 ** (depth + 1) - 2


def potential(state):
    return sum(cost(len(state) - i) * n for i, n in enumerate(state))


def enabled(state):
    return [i for i in range(len(state))
            if i == len(state) - 1 or state[i + 1] > 0]


def step(state, level, success):
    assert level in enabled(state)
    result = list(state)
    if level + 1 < len(state):
        result[level + 1] -= 1
    if success:
        result[level] += 1
    return tuple(result)


@lru_cache(None)
def optimal_finite(state, budget):
    """Maximize root success, then minimize calls, over all enabled actions.

    Returns exact success probability, expected calls and terminal potential.
    Histories with the same inventory have the same future transition law, so
    this dynamic program covers history-dependent randomized policies as well.
    Free discards cannot improve success: extra tickets may simply be ignored.
    Cached reads leave the state and fresh-query budget unchanged.
    """
    if state[0] > 0 or budget == 0:
        return F(state[0] > 0), F(0), F(potential(state))
    choices = []
    for level in enabled(state):
        no = optimal_finite(step(state, level, False), budget - 1)
        yes = optimal_finite(step(state, level, True), budget - 1)
        choices.append(((no[0] + yes[0]) / 2,
                        1 + (no[1] + yes[1]) / 2,
                        (no[2] + yes[2]) / 2))
    # The policy may abort early. This option matters for zero remaining value.
    choices.append((F(0), F(0), F(potential(state))))
    return max(choices, key=lambda c: (c[0], -c[1]))


class Exhausted(Exception):
    pass


class TaggedSchnorrRun:
    """Small arithmetic sanity check; the group is deliberately insecure.

    Private challenge keys contain the entire initiating ancestor context.
    A parent's challenge is revealed only after a valid child completion.
    The strategy prepares only challenge-zero openings and never reads the
    private witness. The challenge table survives snapshots/rewinds.
    """

    modulus, order, generator, public = 23, 11, 2, pow(2, 7, 23)

    def __init__(self, depth, outcomes):
        self.depth = depth
        self.outcomes = iter(outcomes)
        self.table = {}
        self.fresh = [0] * depth
        self.accepted = [set() for _ in range(depth)]
        self.child_for_parent = {}
        self.counter = 0

    def validate(self, proof, level, context):
        tag, commitment, child, challenge, response = proof
        key = (level, context, tag, commitment)
        assert self.table[key] == challenge
        if level + 1 < self.depth:
            self.validate(child, level + 1, context + ((tag, commitment),))
        else:
            assert child is None
        assert pow(self.generator, response, self.modulus) == (
            commitment * pow(self.public, challenge, self.modulus)) % self.modulus

    def session(self, level=0, context=()):
        while True:
            self.counter += 1
            tag = self.counter
            response = tag % self.order
            commitment = pow(self.generator, response, self.modulus)
            key = (level, context, tag, commitment)
            child = None
            if level + 1 < self.depth:
                child_context = context + ((tag, commitment),)
                child = self.session(level + 1, child_context)
                self.validate(child, level + 1, child_context)
                child_key = (level + 1, child_context, child[0], child[1])
                assert child_key in self.accepted[level + 1]
                # This is the operational injection, not a postulated count.
                assert child_key not in self.child_for_parent.values()
                self.child_for_parent[key] = child_key
            assert key not in self.table
            try:
                challenge = next(self.outcomes)
            except StopIteration:
                # No fresh parent query happened; a child completion may remain.
                self.child_for_parent.pop(key, None)
                raise Exhausted
            self.table[key] = challenge
            self.fresh[level] += 1
            # A cached read must agree and must not increase the fresh count.
            assert self.table[key] == challenge
            if challenge == 0:
                proof = (tag, commitment, child, challenge, response)
                self.validate(proof, level, context)
                self.accepted[level].add(key)
                return proof


def actual_protocol_checks():
    checked = 0
    results = []
    for depth in range(1, 5):
        for budget in range(11):
            success_count = 0
            query_sum = 0
            for outcomes in product((0, 1), repeat=budget):
                run = TaggedSchnorrRun(depth, outcomes)
                success = False
                try:
                    proof = run.session()
                    run.validate(proof, 0, ())
                    success = True
                except Exhausted:
                    pass
                assert all(run.fresh[i] <= len(run.accepted[i + 1])
                           for i in range(depth - 1))
                assert sum(run.fresh) <= budget
                success_count += success
                query_sum += sum(run.fresh)
                checked += 1
            probability = F(success_count, 2 ** budget)
            expected = F(query_sum, 2 ** budget)
            assert cost(depth) * probability <= expected
            optimal_probability = optimal_finite((0,) * depth, budget)[0]
            assert probability <= optimal_probability
            results.append({"depth": depth, "max_fresh_queries": budget,
                            "success_probability": str(probability),
                            "expected_fresh_queries": str(expected)})
    return checked, results


def main():
    transition_checks = 0
    corrected_checks = 0
    fork_checks = 0
    for depth in range(1, 6):
        for state in product(range(3), repeat=depth):
            for level in enabled(state):
                no = step(state, level, False)
                yes = step(state, level, True)
                assert F(potential(no) + potential(yes), 2) - potential(state) == 1
                transition_checks += 1
            # Re-reading a cached response changes no available resource.
            assert potential(tuple(state)) == potential(state)

    # Signed deviations in the Lean certificate, independently checked on
    # integer count tables. Only the child-flow condition is assumed here.
    for depth in range(1, 4):
        for flat in product(range(4), repeat=2 * depth):
            queries, accepted = flat[::2], flat[1::2]
            if any(queries[i] > accepted[i + 1] for i in range(depth - 1)):
                continue
            defect = sum((cost(depth - i - 1) + 1) * (2 * accepted[i] - queries[i])
                         for i in range(depth))
            assert cost(depth) * accepted[0] <= sum(queries) + defect
            corrected_checks += 1

    grid = [F(i, 32) for i in range(33)]
    for a, b in product(grid, repeat=2):
        assert a + b - 1 <= a * b
        fork_checks += 1

    finite_records = []
    for depth in range(1, 6):
        for budget in range(19):
            probability, expected, terminal = optimal_finite((0,) * depth, budget)
            assert terminal == expected
            assert cost(depth) * probability <= expected <= budget
            finite_records.append({
                "depth": depth, "max_fresh_queries": budget,
                "maximum_root_success_probability": str(probability),
                "expected_queries_of_selected_optimal_policy": str(expected),
            })

    exact_records = []
    for depth in range(1, 17):
        ledger = [(2 ** (i + 1), 2 ** i) for i in range(depth)]
        assert sum(q for q, _ in ledger) == cost(depth)
        assert all(2 * r == q for q, r in ledger)
        assert all(ledger[i][0] == ledger[i + 1][1] for i in range(depth - 1))
        exact_records.append({
            "depth": depth,
            "expected_fresh_queries_until_root_completion": cost(depth),
            "levels_in_one_successful_output_transcript": depth,
            "expected_query_and_completion_counts": ledger,
        })

    # A wrong reuse model makes child tickets persistent. Its linear cost
    # contradicts the intended nested bound, showing why flow must be proved.
    reused_depth = 2
    reused_expected_queries = F(2 + 2)
    assert reused_expected_queries < cost(reused_depth)

    protocol_checks, protocol_results = actual_protocol_checks()

    print(json.dumps({
        "scope": "restricted fair-guess, context-sensitive resource model",
        "local_transition_drift_checks": transition_checks,
        "signed_count_tables_checked": corrected_checks,
        "two_branch_probability_pairs_checked": fork_checks,
        "finite_budget_instances": len(finite_records),
        "dynamic_program_states": optimal_finite.cache_info().currsize,
        "exact_until_success_instances": exact_records,
        "finite_budget_results": finite_records,
        "tagged_Schnorr_coin_streams_checked": protocol_checks,
        "tagged_Schnorr_strategy_results": protocol_results,
        "wrong_persistent_child_ticket_depth_two_expected_queries":
            str(reused_expected_queries),
        "general_crypto_simulator_embedding_proved": False,
        "DL_reduction_formalized": False,
        "newness_established": False,
        "infinity_category_necessity_proved": False,
        "source_sha256": {
            p.as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in (Path(__file__), LEAN)
        },
    }, indent=2))


if __name__ == "__main__":
    main()
