"""One-probe correction without a challenge table or class masses as input.

The first challenge may depend on both group commitments. Private functions
are fixed under reset. Aborts and arbitrary schedules are outside this model.
Exact full transcript laws, not just acceptance, are compared with honest runs.
"""

from fractions import Fraction as F
from itertools import product
import hashlib
import json
from pathlib import Path
from random import Random


LEAN = Path("Foundation/Examples/ProbeRewindingCorrection.lean")
DEPENDENCY = Path("Foundation/Examples/LocalRewindingCompiler.lean")


def sample(law, rng):
    from math import lcm
    denominator = lcm(*(p.denominator for p in law))
    target = rng.randrange(denominator)
    for i, probability in enumerate(law):
        weight = int(probability * denominator)
        if target < weight:
            return i
        target -= weight
    raise AssertionError("unreachable")


def prepare(public, guess, response):
    return pow(2, response, 7) * pow(pow(public, guess, 7), -1, 7) % 7


class PrivateVerifier:
    def __init__(self, guesses, nx, ny, mode):
        self.guesses = guesses
        self.group = (1, 2, 4)
        rng = Random(9000 + mode)
        self._first = {key: rng.randrange(guesses)
                       for key in product(range(nx), self.group, range(ny), self.group)}
        self._second = {key: rng.randrange(2)
                        for key in product(range(nx), self.group, range(ny), self.group,
                                           range(guesses), range(3))}
        self.first_calls = self.second_calls = 0

    def first(self, x, a, y, b):
        self.first_calls += 1
        return self._first[x, a, y, b]

    def second(self, public, x, a, y, b, challenge_a, response_a):
        assert challenge_a == self._first[x, a, y, b]
        assert pow(2, response_a, 7) == a * pow(public, challenge_a, 7) % 7
        self.second_calls += 1
        return self._second[x, a, y, b, challenge_a, response_a]


def execute_probe(law_x, law_y, public, verifier, rng):
    """Uses only oracle replies; no mass, table, or secret argument is supplied."""
    while True:
        x, guess_a, response_a = sample(law_x, rng), rng.randrange(verifier.guesses), rng.randrange(3)
        a = prepare(public, guess_a, response_a)
        pilot_y, pilot_b = sample(law_y, rng), pow(2, rng.randrange(3), 7)
        pilot_challenge = verifier.first(x, a, pilot_y, pilot_b)
        if pilot_challenge == guess_a and rng.randrange(2) != 0:
            continue
        while True:
            y, guess_b, response_b = sample(law_y, rng), rng.randrange(2), rng.randrange(3)
            b = prepare(public, guess_b, response_b)
            challenge_a = verifier.first(x, a, y, b)
            if challenge_a != guess_a:
                break
            challenge_b = verifier.second(public, x, a, y, b, challenge_a, response_a)
            if challenge_b == guess_b:
                assert pow(2, response_b, 7) == b * pow(public, challenge_b, 7) % 7
                return x, a, y, b, challenge_a, response_a, challenge_b, response_b


def exact_law(law_x, law_y, secret, verifier):
    q, p = 3, F(1, 2)
    public = pow(2, secret, 7)
    raw_outputs = {}
    raw_pilot_cost, raw_main_cost = F(1), F(0)
    for x, guess_a, response_a in product(range(len(law_x)), range(verifier.guesses), range(q)):
        base = law_x[x] / (verifier.guesses * q)
        a = prepare(public, guess_a, response_a)
        accept_probe = F(0)
        for pilot_y, pilot_nonce in product(range(len(law_y)), range(q)):
            pilot_b = pow(2, pilot_nonce, 7)
            challenge = verifier.first(x, a, pilot_y, pilot_b)
            accept_probe += law_y[pilot_y] / q * (p if challenge == guess_a else 1)
        loop, immediate_cost, exits = F(0), F(0), {}
        for y, guess_b, response_b in product(range(len(law_y)), (0, 1), range(q)):
            probability = law_y[y] / (2 * q)
            b = prepare(public, guess_b, response_b)
            challenge_a = verifier.first(x, a, y, b)
            immediate_cost += probability
            if challenge_a != guess_a:
                continue
            challenge_b = verifier.second(public, x, a, y, b, challenge_a, response_a)
            immediate_cost += probability
            if guess_b != challenge_b:
                loop += probability
                continue
            transcript = (x, a, y, b, challenge_a, response_a, challenge_b, response_b)
            exits[transcript] = exits.get(transcript, F(0)) + probability
        # The correction is constructed by a pilot query, not by this equality.
        assert accept_probe == 1 - loop
        for transcript, probability in exits.items():
            raw_outputs[transcript] = raw_outputs.get(transcript, F(0)) + (
                base * accept_probe * probability / (1 - loop))
        raw_main_cost += base * accept_probe * immediate_cost / (1 - loop)
    success = sum(raw_outputs.values())
    assert success == p / verifier.guesses
    observed = {t: value / success for t, value in raw_outputs.items()}
    honest = {}
    for x, y, nonce_a, nonce_b in product(range(len(law_x)), range(len(law_y)), range(q), range(q)):
        a, b = pow(2, nonce_a, 7), pow(2, nonce_b, 7)
        challenge_a = verifier.first(x, a, y, b)
        response_a = (nonce_a + challenge_a * secret) % q
        challenge_b = verifier.second(public, x, a, y, b, challenge_a, response_a)
        response_b = (nonce_b + challenge_b * secret) % q
        transcript = (x, a, y, b, challenge_a, response_a, challenge_b, response_b)
        honest[transcript] = honest.get(transcript, F(0)) + law_x[x] * law_y[y] / (q * q)
    assert observed == honest
    pilot_cost, main_cost = raw_pilot_cost / success, raw_main_cost / success
    assert pilot_cost == verifier.guesses / p
    assert main_cost == (verifier.guesses + 1) / p
    return {"first_challenge_values": verifier.guesses,
            "pilot_expected_challenge_calls": str(pilot_cost),
            "main_expected_challenge_calls": str(main_cost),
            "total_expected_challenge_calls": str(pilot_cost + main_cost),
            "full_restart_expected_challenge_calls": str((verifier.guesses + 1) / p)}


def main():
    laws_x = [(F(1, 2),) * 2, (F(1, 3), F(2, 3))]
    laws_y = [(F(1, 3),) * 3, (F(1, 6), F(1, 3), F(1, 2))]
    full_laws, executions = 0, 0
    costs = {}
    for guesses, mode, secret, law_x, law_y in product((2, 3), range(8), range(3), laws_x, laws_y):
        verifier = PrivateVerifier(guesses, len(law_x), len(law_y), mode)
        record = exact_law(law_x, law_y, secret, verifier)
        costs[guesses] = record
        full_laws += 1
        if secret == 1 and law_x == laws_x[0] and law_y == laws_y[0]:
            for seed in range(4):
                independent = PrivateVerifier(guesses, len(law_x), len(law_y), mode)
                output = execute_probe(law_x, law_y, pow(2, secret, 7), independent, Random(seed))
                assert output[4] == independent._first[output[:4]]
                executions += 1
    print(json.dumps({
        "complete_Schnorr_transcript_laws_checked": full_laws,
        "oracle_only_witness_free_sampler_checks": executions,
        "private_functions_depend_on_group_commitments": True,
        "second_private_function_also_depends_on_first_response": True,
        "sampler_requires_class_masses_or_global_coupling": False,
        "cost_comparison": list(costs.values()),
        "faster_than_full_restart": False,
        "scope": "two sessions, fixed crossing schedule, fixed private challenge functions, no verifier aborts",
        "secret_group_for_tests": "order 3 subgroup modulo 7; not a hardness experiment",
        "operational_sampler_Lean_checked": False,
        "arbitrary_schedule_or_abort_support_proved": False,
        "newness_established": False,
        "infinity_category_necessity_proved": False,
        "source_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__), LEAN, DEPENDENCY)},
    }, indent=2))


if __name__ == "__main__":
    main()
