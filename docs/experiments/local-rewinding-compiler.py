"""Generate both proposal corrections from a finite local challenge table.

The independently built absorbing chain checks final output laws and costs.
Complete small Schnorr transcript laws are checked separately, including a
second challenge depending on group commitments and the first response.
No generic black-box ZK or infinity-category novelty is claimed.
"""

from fractions import Fraction as F
from itertools import product
from math import lcm
import hashlib
import json
from pathlib import Path
from random import Random


LEAN = Path("Foundation/Examples/LocalRewindingCompiler.lean")


def solve_many(matrix, targets):
    n = len(matrix)
    rows = [[F(v) for v in a] + [F(v) for v in b]
            for a, b in zip(matrix, targets)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if rows[i][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        scale = rows[col][col]
        rows[col] = [v / scale for v in rows[col]]
        for i in range(n):
            if i != col and rows[i][col]:
                scale = rows[i][col]
                rows[i] = [a - scale * b for a, b in zip(rows[i], rows[col])]
    answer = [row[n:] for row in rows]
    assert all(sum(matrix[i][j] * answer[j][k] for j in range(n)) == targets[i][k]
               for i in range(n) for k in range(len(targets[0])))
    return answer


def compile_local(table, law_x, law_y, p):
    nx, ny = len(law_x), len(law_y)
    challenges = sorted(set(c for row in table for c in row))
    mass, denominator, row_weight, guesses = {}, {}, {}, {}
    for x in range(nx):
        for c in challenges:
            mass[x, c] = sum(law_y[y] for y in range(ny) if table[x][y] == c)
            denominator[x, c] = 1 - (1 - p) * mass[x, c]
        row_weight[x] = sum(denominator[x, c] for c in challenges if mass[x, c])
        for c in challenges:
            guesses[x, c] = denominator[x, c] / row_weight[x] if mass[x, c] else F(0)
        assert sum(guesses[x, c] for c in challenges) == 1
    total = sum(law_x[x] * row_weight[x] for x in range(nx))
    contexts = {x: law_x[x] * row_weight[x] / total for x in range(nx)}
    proposal = {(x, c): contexts[x] * guesses[x, c]
                for x in range(nx) for c in challenges if guesses[x, c]}
    assert sum(contexts.values()) == sum(proposal.values()) == 1
    for x, y in product(range(nx), range(ny)):
        c = table[x][y]
        unnormalized = (proposal[x, c] * law_y[y] * p / denominator[x, c])
        assert unnormalized == law_x[x] * law_y[y] * p / total
    mean_classes = sum(law_x[x] * sum(mass[x, c] > 0 for c in challenges)
                       for x in range(nx))
    return {"mass": mass, "denominator": denominator,
            "row_weight": row_weight, "total_weight": total,
            "contexts": contexts, "guesses": guesses, "proposal": proposal,
            "success_mass": p / total,
            "expected_checks": (mean_classes + 1) / p,
            "lookahead_expected_checks": 2 / p}


def independent_chain(table, law_x, law_y, p, proposal):
    """Build transitions by sampling y and the second result, not class formulas."""
    states = sorted(proposal)
    outputs = list(product(range(len(law_x)), range(len(law_y))))
    state_index = {s: i for i, s in enumerate(states)}
    output_index = {s: i for i, s in enumerate(outputs)}
    matrix, targets = [], []
    for x, c in states:
        i = state_index[x, c]
        transition = [F(0)] * len(states)
        rhs = [F(0)] * (len(outputs) + 1)
        for y, probability in enumerate(law_y):
            rhs[-1] += probability  # first challenge check
            if table[x][y] != c:
                for target, weight in proposal.items():
                    transition[state_index[target]] += probability * weight
            else:
                rhs[-1] += probability  # second challenge check
                transition[i] += probability * (1 - p)
                rhs[output_index[x, y]] += probability * p
        assert sum(transition) + sum(rhs[:-1]) == 1
        row = [-v for v in transition]
        row[i] += 1
        matrix.append(row)
        targets.append(rhs)
    values = solve_many(matrix, targets)
    result = [sum(proposal[s] * values[state_index[s]][k] for s in states)
              for k in range(len(outputs) + 1)]
    law = dict(zip(outputs, result[:-1]))
    assert sum(law.values()) == 1
    return law, result[-1]


def exact_sample(weights, rng):
    denominator = lcm(*(v.denominator for v in weights.values()))
    integer_weights = [(key, int(value * denominator)) for key, value in weights.items()]
    target = rng.randrange(sum(v for _, v in integer_weights))
    for key, weight in integer_weights:
        if target < weight:
            return key
        target -= weight
    raise AssertionError("unreachable")


def prepare(public, guess, response, modulus=7, generator=2):
    return pow(generator, response, modulus) * pow(pow(public, guess, modulus), -1, modulus) % modulus


def second_challenge(x, a, y, b, first_challenge, first_response, mode):
    return (mode + (mode + 1) * x + 3 * a + 5 * y +
            (mode + 2) * b + first_challenge + first_response) % 2


def full_transcript_law(table, law_x, law_y, compiled, secret, mode):
    """Enumerate actual group proposals, independently of the abstract chain."""
    q, modulus, generator = 3, 7, 2
    public = pow(generator, secret, modulus)
    mass, raw_cost = {}, F(0)
    for (x, guess_a), weight in compiled["proposal"].items():
        for response_a in range(q):
            a = prepare(public, guess_a, response_a)
            loop, immediate_cost, exits = F(0), F(0), {}
            for y, guess_b, response_b in product(range(len(law_y)), (0, 1), range(q)):
                probability = law_y[y] / (2 * q)
                b = prepare(public, guess_b, response_b)
                challenge_a = table[x][y]
                immediate_cost += probability
                if guess_a != challenge_a:
                    continue
                assert pow(generator, response_a, modulus) == a * pow(public, challenge_a, modulus) % modulus
                challenge_b = second_challenge(x, a, y, b, challenge_a, response_a, mode)
                immediate_cost += probability
                if guess_b != challenge_b:
                    loop += probability
                    continue
                assert pow(generator, response_b, modulus) == b * pow(public, challenge_b, modulus) % modulus
                transcript = (x, a, y, b, challenge_a, response_a, challenge_b, response_b)
                exits[transcript] = exits.get(transcript, F(0)) + probability
            for transcript, probability in exits.items():
                mass[transcript] = mass.get(transcript, F(0)) + weight / q * probability / (1 - loop)
            raw_cost += weight / q * immediate_cost / (1 - loop)
    success_mass = sum(mass.values())
    observed = {key: value / success_mass for key, value in mass.items()}
    honest = {}
    for x, y, random_a, random_b in product(range(len(law_x)), range(len(law_y)), range(q), range(q)):
        a, b = pow(generator, random_a, modulus), pow(generator, random_b, modulus)
        challenge_a = table[x][y]
        response_a = (random_a + challenge_a * secret) % q
        challenge_b = second_challenge(x, a, y, b, challenge_a, response_a, mode)
        response_b = (random_b + challenge_b * secret) % q
        transcript = (x, a, y, b, challenge_a, response_a, challenge_b, response_b)
        honest[transcript] = honest.get(transcript, F(0)) + law_x[x] * law_y[y] / (q * q)
    assert observed == honest
    assert raw_cost / success_mass == compiled["expected_checks"]


def execute_generated(table, law_x, law_y, compiled, public, mode, rng, lookahead=False):
    """An executable witness-free sampler; the secret is not an argument."""
    while True:
        if lookahead:
            x = exact_sample(dict(enumerate(law_x)), rng)
            fixed_y = exact_sample(dict(enumerate(law_y)), rng)
            guess_a = table[x][fixed_y]
        else:
            x, guess_a = exact_sample(compiled["proposal"], rng)
        response_a = rng.randrange(3)
        a = prepare(public, guess_a, response_a)
        while True:
            y = fixed_y if lookahead else exact_sample(dict(enumerate(law_y)), rng)
            guess_b, response_b = rng.randrange(2), rng.randrange(3)
            b = prepare(public, guess_b, response_b)
            challenge_a = table[x][y]
            if challenge_a != guess_a:
                break
            challenge_b = second_challenge(x, a, y, b, challenge_a, response_a, mode)
            if challenge_b == guess_b:
                assert pow(2, response_a, 7) == a * pow(public, challenge_a, 7) % 7
                assert pow(2, response_b, 7) == b * pow(public, challenge_b, 7) % 7
                return x, a, y, b, challenge_a, response_a, challenge_b, response_b


def laws(n):
    uniform = tuple(F(1, n) for _ in range(n))
    ramp = tuple(F(i + 1, n * (n + 1) // 2) for i in range(n))
    return [uniform] if uniform == ramp else [uniform, ramp]


def main():
    checked, biases, strict_dominance = 0, 0, 0
    full_laws, execution_checks = 0, 0
    binary_tables = []
    for nx, ny, nc in product((1, 2), (1, 2, 3), (1, 2, 3)):
        for flat in product(range(nc), repeat=nx * ny):
            table = tuple(tuple(flat[x * ny:(x + 1) * ny]) for x in range(nx))
            for law_x, law_y, p in product(laws(nx), laws(ny), (F(1, 2), F(1, 3), F(1))):
                compiled = compile_local(table, law_x, law_y, p)
                output, cost = independent_chain(table, law_x, law_y, p, compiled["proposal"])
                assert output == {(x, y): law_x[x] * law_y[y] for x, y in output}
                assert cost == compiled["expected_checks"]
                assert compiled["lookahead_expected_checks"] <= cost
                strict_dominance += compiled["lookahead_expected_checks"] < cost
                checked += 1
            if (nx, ny, nc) == (2, 3, 2):
                binary_tables.append(table)
    law_x, law_y = (F(1, 2),) * 2, (F(1, 3),) * 3
    for table in binary_tables:
        compiled = compile_local(table, law_x, law_y, F(1, 2))
        for secret, mode in product(range(3), range(2)):
            full_transcript_law(table, law_x, law_y, compiled, secret, mode)
            full_laws += 1
        for seed, lookahead in product(range(3), (False, True)):
            execute_generated(table, law_x, law_y, compiled, pow(2, 1, 7), 1,
                              Random(seed), lookahead=lookahead)
            execution_checks += 1
    unequal_table = ((0, 1, 1),)
    uniform_proposal = {(0, 0): F(1, 2), (0, 1): F(1, 2)}
    wrong, _ = independent_chain(unequal_table, (F(1),), law_y, F(1, 2), uniform_proposal)
    assert wrong == {(0, 0): F(2, 7), (0, 1): F(5, 14), (0, 2): F(5, 14)}
    unequal = compile_local(unequal_table, (F(1),), law_y, F(1, 2))
    assert unequal["guesses"][0, 0] == F(5, 9)
    previous = compile_local(((0, 0), (0, 1)), (F(1, 2),) * 2, (F(1, 2),) * 2, F(1, 2))
    assert previous["contexts"][0] == F(1, 4)
    assert previous["expected_checks"] == 5
    print(json.dumps({
        "finite_local_tables_and_laws_checked": checked,
        "independent_verification": "absorbing-chain equations for every output probability and expected cost",
        "lookahead_strictly_cheaper_instances": strict_dominance,
        "lookahead_never_more_expensive": True,
        "complete_Schnorr_transcript_laws_checked": full_laws,
        "executable_witness_free_sampler_checks": execution_checks,
        "unequal_classes": {
            "uncorrected_output_law": {str(k): str(v) for k, v in wrong.items()},
            "corrected_guess_distribution": {str(c): str(v) for (_, c), v in unequal["guesses"].items()},
            "exact_expected_checks": str(unequal["expected_checks"]),
        },
        "previous_example_joint_correction": {
            "context_zero_probability": str(previous["contexts"][0]),
            "joint_proposal": {str(k): str(v) for k, v in previous["proposal"].items()},
            "expected_checks": str(previous["expected_checks"]),
            "lookahead_expected_checks": str(previous["lookahead_expected_checks"]),
        },
        "scope": "known finite first-challenge table depending only on public tags; fixed two-stage restart structure",
        "preprocessing_oracle_queries_in_cost": False,
        "generic_adaptive_or_commitment_dependent_verifier_supported": False,
        "full_machine_semantics_Lean_checked": False,
        "newness_established": False,
        "infinity_category_necessity_proved": False,
        "source_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__), LEAN)},
    }, indent=2))


if __name__ == "__main__":
    main()
