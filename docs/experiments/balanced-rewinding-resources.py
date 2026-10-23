"""Exact transcript laws and operation counts for balanced crossing rewinding.

A uniform public tag is transformed by a private permutation depending on both
commitments. The sampler sees only challenge callbacks. No class-mass input,
secret input, pilot query, or global coupling is supplied to the sampler.
This is a fixed two-session schedule with no aborts and abstract state reset.
"""
from fractions import Fraction as F
from itertools import product, permutations
from random import Random
from pathlib import Path
import hashlib
import json

GROUP = (1, 2, 4)
Q = 3
LEAN = Path('Foundation/Examples/BalancedRewindingResources.lean')
DEPENDENCY = Path('Foundation/Examples/LocalRewindingCompiler.lean')
KEYS = tuple(product(GROUP, repeat=2))


def prepare(public, guess, response):
    return pow(2, response, 7) * pow(pow(public, guess, 7), -1, 7) % 7


class Verifier:
    def __init__(self, k, kb, table, seed):
        self.k, self.kb = k, kb
        self._table = dict(zip(KEYS, table))
        rng = Random(seed)
        self._second = {key: rng.randrange(kb) for key in
                        product(GROUP, GROUP, range(k), range(k), range(Q))}
        self.qa = self.qb = 0

    def first(self, a, b, tag):
        self.qa += 1
        return self._table[a, b][tag]

    def second(self, public, a, b, tag, challenge, response):
        assert challenge == self._table[a, b][tag]
        assert pow(2, response, 7) == a * pow(public, challenge, 7) % 7
        self.qb += 1
        return self._second[a, b, tag, challenge, response]


def honest_law(secret, verifier):
    public = pow(2, secret, 7)
    law = {}
    for ra, rb, tag in product(range(Q), range(Q), range(verifier.k)):
        a, b = pow(2, ra, 7), pow(2, rb, 7)
        ca = verifier.first(a, b, tag)
        za = (ra + ca * secret) % Q
        cb = verifier.second(public, a, b, tag, ca, za)
        zb = (rb + cb * secret) % Q
        law[a, b, tag, ca, za, cb, zb] = F(1, Q * Q * verifier.k)
    assert sum(law.values()) == 1
    return law


def exact_reuse(secret, verifier):
    k, kb, public = verifier.k, verifier.kb, pow(2, secret, 7)
    raw, costs = {}, dict.fromkeys(('a', 'b', 'qa', 'qb', 'root', 'local', 'snapshot'), F(0))
    for ua, za in product(range(k), range(Q)):
        a = prepare(public, ua, za)
        base = F(1, k * Q)
        loop = fail = calls_b = F(0)
        exits = {}
        for tag, ub, zb in product(range(k), range(kb), range(Q)):
            probability = F(1, k * kb * Q)
            b = prepare(public, ub, zb)
            ca = verifier.first(a, b, tag)
            if ca != ua:
                fail += probability
                continue
            calls_b += probability
            cb = verifier.second(public, a, b, tag, ca, za)
            if cb != ub:
                loop += probability
                continue
            t = (a, b, tag, ca, za, cb, zb)
            exits[t] = exits.get(t, F(0)) + probability
        # Independent absorbing-chain solution for each prepared A candidate.
        assert fail + loop + sum(exits.values()) == 1
        for t, probability in exits.items():
            raw[t] = raw.get(t, F(0)) + base * probability / (1 - loop)
        costs['a'] += base
        costs['snapshot'] += base
        for metric in ('b', 'qa'):
            costs[metric] += base / (1 - loop)
        costs['qb'] += base * calls_b / (1 - loop)
        costs['root'] += base * fail / (1 - loop)
        costs['local'] += base * loop / (1 - loop)
    success = sum(raw.values())
    costs = {key: value / success for key, value in costs.items()}
    law = {t: probability / success for t, probability in raw.items()}
    p = F(1, kb)
    assert success == p / (k - 1 + p)
    assert costs == {'a': (k - 1 + p) / p, 'b': k / p,
                     'qa': k / p, 'qb': 1 / p, 'root': (k - 1) / p,
                     'local': (1 - p) / p, 'snapshot': (k - 1 + p) / p}
    return law, costs


def exact_full_restart(secret, verifier):
    k, kb, public = verifier.k, verifier.kb, pow(2, secret, 7)
    raw, second_calls = {}, F(0)
    for ua, za, tag, ub, zb in product(range(k), range(Q), range(k), range(kb), range(Q)):
        probability = F(1, k * Q * k * kb * Q)
        a, b = prepare(public, ua, za), prepare(public, ub, zb)
        ca = verifier.first(a, b, tag)
        if ca != ua:
            continue
        second_calls += probability
        cb = verifier.second(public, a, b, tag, ca, za)
        if cb == ub:
            t = (a, b, tag, ca, za, cb, zb)
            raw[t] = raw.get(t, F(0)) + probability
    success = sum(raw.values())
    p = F(1, kb)
    assert success == p / k
    costs = {'a': 1 / success, 'b': 1 / success, 'qa': 1 / success,
             'qb': second_calls / success, 'root': (1 - success) / success,
             'local': F(0), 'snapshot': F(0)}
    return {t: probability / success for t, probability in raw.items()}, costs


def execute(public, verifier, rng, reuse):
    """No secret, class masses, permutation table, or pilot calls are inputs."""
    counts = dict.fromkeys(('a', 'b', 'root', 'local', 'snapshot'), 0)
    while True:
        ua, za = rng.randrange(verifier.k), rng.randrange(Q)
        a = prepare(public, ua, za)
        counts['a'] += 1
        counts['snapshot'] += int(reuse)
        while True:
            tag, ub, zb = rng.randrange(verifier.k), rng.randrange(verifier.kb), rng.randrange(Q)
            b = prepare(public, ub, zb)
            counts['b'] += 1
            ca = verifier.first(a, b, tag)
            if ca != ua:
                counts['root'] += 1
                break
            cb = verifier.second(public, a, b, tag, ca, za)
            if cb == ub:
                assert pow(2, zb, 7) == b * pow(public, cb, 7) % 7
                counts.update(qa=verifier.qa, qb=verifier.qb)
                return (a, b, tag, ca, za, cb, zb), counts
            if reuse:
                counts['local'] += 1
            else:
                counts['root'] += 1
                break


def weighted(costs, weights):
    return sum(costs[name] * value for name, value in weights.items())


def main():
    cases = executions = 0
    examples = {}
    binary_perms = tuple(permutations(range(2)))
    tables = [(2, table) for table in product(binary_perms, repeat=len(KEYS))]
    rng = Random(4934)
    ternary_perms = tuple(permutations(range(3)))
    tables += [(3, tuple(rng.choice(ternary_perms) for _ in KEYS)) for _ in range(24)]
    for index, (k, table) in enumerate(tables):
        for kb, secret, second_seed in product((2, 3), range(Q), (0, 1)):
            v = Verifier(k, kb, table, second_seed)
            honest = honest_law(secret, v)
            observed, reuse = exact_reuse(secret, v)
            baseline, full = exact_full_restart(secret, v)
            assert observed == baseline == honest
            assert full['qa'] == reuse['qa'] and full['qb'] == reuse['qb']
            assert full['b'] == reuse['b']
            assert full['a'] - reuse['a'] == kb - 1
            assert full['root'] + full['local'] == reuse['root'] + reuse['local']
            p = F(1, kb)
            # Include both favourable and unfavourable snapshot/restore costs.
            for a, root, local, snapshot in ((10, 2, 2, 1), (1, 2, 2, 1), (10, 1, 20, 0)):
                weights = {'a': F(a), 'b': F(7), 'qa': F(2), 'qb': F(3),
                           'root': F(root), 'local': F(local), 'snapshot': F(snapshot)}
                gap = weighted(full, weights) - weighted(reuse, weights)
                assert gap == ((1 - p) * (a + root - local) - snapshot * (k - 1 + p)) / p
            examples[k, kb] = {'A_challenges': k, 'B_challenges': kb,
                               'full_restart': {key: str(val) for key, val in full.items()},
                               'balanced_reuse': {key: str(val) for key, val in reuse.items()}}
            cases += 1
            if index % 32 == 0 and secret == 1 and second_seed == 0:
                for method in (False, True):
                    vv = Verifier(k, kb, table, second_seed)
                    transcript, counts = execute(pow(2, secret, 7), vv, Random(index + kb), method)
                    assert transcript in honest
                    assert counts['qa'] == counts['b']
                    assert counts['root'] + counts['local'] + 1 == counts['b']
                    executions += 1
    print(json.dumps({
        'complete_transcript_laws_checked': cases,
        'binary_first_challenge_permutation_tables_exhausted': 512,
        'ternary_first_challenge_permutation_tables_sampled': 24,
        'executable_witness_free_sampler_checks': executions,
        'no_pilot_queries_or_class_mass_inputs': True,
        'exact_resource_comparisons': list(examples.values()),
        'weighted_snapshot_and_restore_cost_cases_per_setting': 3,
        'group_for_tests': 'order 3 subgroup modulo 7; no hardness experiment',
        'scope': 'private commitment-dependent permutations of a uniform public tag; fixed crossing schedule; no aborts; abstract reset',
        'universal_simulator_optimality_proved': False,
        'wall_clock_advantage_established': False,
        'full_machine_semantics_Lean_checked': False,
        'newness_established': False,
        'infinity_category_necessity_proved': False,
        'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__), LEAN, DEPENDENCY)},
    }, indent=2))


if __name__ == '__main__':
    main()
