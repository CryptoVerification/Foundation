"""Exact algebra for a classical comparison, with explicit bridge limitations.

N labeled classical keys, a one-bit message/ciphertext, reversible branches,
variable key probabilities, and zero-probability branches identified. Finite
checks do not prove homotopy claims or implement a bounded fair-coin sampler.
"""
from fractions import Fraction as F
from pathlib import Path
from random import Random
import hashlib
import json


def normalize(vector):
    length = sum(abs(x) for x in vector)
    assert length > 0
    return [x/length for x in vector]


def cipher_check(vector):
    assert sum(vector) == 0 and sum(abs(x) for x in vector) == 1
    weights = list(map(abs, vector))
    for message in (0, 1):
        ciphertext = [F(0), F(0)]
        for signed, weight in zip(vector, weights):
            flip = int(signed < 0)
            encrypted = message ^ flip
            ciphertext[encrypted] += weight
            if weight:
                assert (encrypted ^ flip) == message
        assert ciphertext == [F(1, 2), F(1, 2)]


def added_key_homotopy(vector, time):
    keys = len(vector)
    center = [F(1, 2*keys)]*keys+[-F(1, 2)]
    return normalize([(1-time)*a+time*b for a, b in zip(vector+[F(0)], center)])


def sorted_contraction(vector, time):
    ordered = sorted(vector)
    center = [-F(1, 2)]+[F(0)]*(len(vector)-2)+[F(1, 2)]
    return normalize([(1-time)*a+time*b for a, b in zip(ordered, center)])


def digital_tetrahedron(bits):
    # Each row has norm 1, zero sum, and dyadic key probabilities. The four
    # rows have barycenter zero. Their hull supplies the degree-one boundary.
    total = 2**bits
    rest, remainder = divmod(total//2, 3)
    positive = [rest+int(i < remainder) for i in range(3)]
    row = [-F(1, 2)]+[F(x, total) for x in positive]
    return [row[i:]+row[:i] for i in range(4)]


def digital_checks():
    settings = samples = 0
    worst_gap = F(0)
    for bits in range(3, 11):
        vertices = digital_tetrahedron(bits)
        assert all(sum(v[j] for v in vertices) == 0 for j in range(4))
        pair_distance = max(sum(abs(x-y) for x, y in zip(a, b))/2 for a in vertices for b in vertices)
        assert F(2, 3) <= pair_distance <= F(2, 3)+F(4, 2**bits)
        worst_gap = max(worst_gap, pair_distance-F(2, 3))
        for vertex in vertices:
            cipher_check(vertex)
            counts = [int(abs(x)*2**bits) for x in vertex]
            assert sum(counts) == 2**bits
            outputs = [0]*4
            # Exact B-fair-coin key sampler: interpret the bits as an integer,
            # then use at most three cumulative comparisons. No rejection.
            for value in range(2**bits):
                cutoff = 0
                for key, count in enumerate(counts):
                    cutoff += count
                    if value < cutoff:
                        outputs[key] += 1
                        break
                else:
                    raise AssertionError('sampler did not return')
                samples += 1
            assert outputs == counts
            settings += 1
    sharp = [[-F(1, 2) if i == j else F(1, 6) for j in range(4)] for i in range(4)]
    assert all(sum(v[j] for v in sharp) == 0 for j in range(4))
    assert max(sum(abs(x-y) for x, y in zip(a, b))/2 for a in sharp for b in sharp) == F(2, 3)
    return {'dyadic_tetrahedron_vertex_samplers': settings,
            'enumerated_fair_coin_outcomes': samples,
            'coin_budget_range': [3, 10],
            'sharp_simplex_jump_in_joint_key_ciphertext_TV': '2/3',
            'largest_tested_dyadic_excess_over_sharp_jump': str(worst_gap),
            'sampler_rejection_or_unbounded_loop': False}


def checks():
    rng = Random(20261023)
    ciphers = added = sorted_cases = 0
    for keys in range(2, 9):
        for _ in range(64):
            raw = [rng.randrange(-10, 11) for _ in range(keys)]
            if len(set(raw)) == 1:
                raw[0] += 1
            mean = F(sum(raw), keys)
            vector = normalize([F(x)-mean for x in raw])
            cipher_check(vector)
            ciphers += 1
            for step in range(17):
                time = F(step, 16)
                filled = added_key_homotopy(vector, time)
                cipher_check(filled)
                if not time:
                    assert filled == vector+[F(0)]
                if time == 1:
                    assert filled == [F(1, 2*keys)]*keys+[-F(1, 2)]
                added += 1
                contracted = sorted_contraction(vector, time)
                cipher_check(contracted)
                assert contracted == sorted(contracted)
                if not time:
                    assert contracted == sorted(vector)
                if time == 1:
                    assert contracted == [-F(1, 2)]+[F(0)]*(keys-2)+[F(1, 2)]
                sorted_cases += 1
    vertices = [[F(1, 2), -F(1, 2), F(0)], [F(1, 2), F(0), -F(1, 2)],
                [F(0), F(1, 2), -F(1, 2)], [-F(1, 2), F(1, 2), F(0)],
                [-F(1, 2), F(0), F(1, 2)], [F(0), -F(1, 2), F(1, 2)]]
    hexagon = 0
    for a, b in zip(vertices, vertices[1:]+vertices[:1]):
        for step in range(17):
            time = F(step, 16)
            cipher_check([(1-time)*x+time*y for x, y in zip(a, b)])
            hexagon += 1
    non_dyadic = [F(1, 3), F(1, 6), -F(1, 2)]
    cipher_check(non_dyadic)
    for bits in range(33):
        assert (abs(non_dyadic[0])*2**bits).denominator != 1
    return {'exact_private_correct_labeled_ciphers': ciphers,
            'key_alphabet_sizes': list(range(2, 9)),
            'one_added_key_homotopy_settings': added,
            'key_relabeling_quotient_contraction_settings': sorted_cases,
            'three_key_hexagon_edge_settings': hexagon,
            'non_dyadic_valid_key_probabilities': ['1/3', '1/6', '1/2'],
            'checked_non_dyadic_coin_counts': list(range(33))}


def main():
    result = {'exact_rational_checks': checks(), 'digital_checks': digital_checks(),
              'mathematical_classification': 'The space of labeled reversible perfect one-bit ciphers with N keys and variable probabilities is {d: sum d=0, sum |d|=1}, homeomorphic to S^(N-2).',
              'key_relabeling_quotient': 'contractible, via sorting and normalized interpolation',
              'one_additional_key_inclusion': 'nullhomotopic via the explicit normalized interpolation',
              'digital_mathematical_claim': 'A tetrahedralized 3-ball whose normalized four-key boundary has degree one must contain a simplex edge with joint key/ciphertext TV distance at least 2/3. The same bound holds for a nonnull boundary sphere of any dimension, by a three-dimensional Caratheodory reduction.',
              'unrestricted_classical_cryptography_requires_higher_categories': False,
              'existing_PPT_machine_backend_connected': False,
              'bounded_fair_coin_exact_sampler_for_all_inputs': False,
              'topological_claims_computer_verified': False,
              'Lean_checked': False, 'newness_established': False,
              'source_sha256': {str(Path(__file__).resolve()): hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
