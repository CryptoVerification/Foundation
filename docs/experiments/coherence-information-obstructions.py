"""Exact witnesses that endpoint laws lose composition-relevant information.

Cycle couplings: exact minimax pairwise total-variation loss d / length, with
an explicit attaining joint law and pointwise lower-bound certificate.
Quantum example: erasing global phase is incompatible with adding control.
Neither calculation establishes infinity-category necessity or crypto novelty.
"""
from fractions import Fraction as F
from itertools import permutations, product
from collections import Counter
from random import Random
from pathlib import Path
import hashlib
import json


def holonomy(edges, value):
    for edge in edges:
        value = edge[value]
    return value


def defects(edges, state):
    return sum(state[(i + 1) % len(edges)] != edge[state[i]] for i, edge in enumerate(edges))


def check_cycle(edges, exhaustive_atoms):
    n, length = len(edges[0]), len(edges)
    mismatch = sum(holonomy(edges, x) != x for x in range(n))
    # Pick one edge to break uniformly; propagate along all remaining edges.
    counts = Counter()
    for broken, seed in product(range(length), range(n)):
        state = [None] * length
        state[(broken + 1) % length] = seed
        for step in range(1, length):
            index = (broken + step) % length
            state[(index + 1) % length] = edges[index][state[index]]
        counts[tuple(state)] += 1
    assert sum(counts.values()) == length * n
    for index, edge in enumerate(edges):
        marginal = Counter()
        pair = Counter()
        for state, count in counts.items():
            marginal[state[index]] += count
            pair[state[index], state[(index + 1) % length]] += count
        assert marginal == Counter({x: length for x in range(n)})
        target = Counter({(x, edge[x]): length for x in range(n)})
        tv = sum(abs(pair[key] - target[key]) for key in pair.keys() | target.keys()) / F(2 * length * n)
        assert tv == F(mismatch, n * length)
    # A dual certificate: impossible closure forces some violated edge.
    atoms = product(range(n), repeat=length) if exhaustive_atoms else counts.keys()
    checked = 0
    for state in atoms:
        assert int(holonomy(edges, state[0]) != state[0]) <= defects(edges, state)
        checked += 1
    return mismatch, checked


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def transpose(a):
    return tuple(zip(*a))


def neg(a):
    return tuple(tuple(-x for x in row) for row in a)


def kron(a, b):
    return tuple(tuple(x * y for x in row_a for y in row_b)
                 for row_a in a for row_b in b)


def channel(u, a):
    return mm(mm(u, a), transpose(u))


def controlled(u):
    return tuple(tuple((int(i == j) if i < 2 and j < 2 else
                        u[i - 2][j - 2] if i >= 2 and j >= 2 else 0)
                       for j in range(4)) for i in range(4))


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def quantum_witness():
    identity = ((1, 0), (0, 1))
    x = ((0, 1), (1, 0))
    z = ((1, 0), (0, -1))
    basis = [tuple(tuple(int(i == r and j == c) for j in range(2)) for i in range(2))
             for r, c in product(range(2), repeat=2)]
    for atom in basis:
        assert channel(identity, atom) == channel(neg(identity), atom)
        assert channel(mm(x, z), atom) == channel(mm(z, x), atom)
    plus = ((F(1, 2), F(1, 2)), (F(1, 2), F(1, 2)))
    zero = ((1, 0), (0, 0))
    input_density = kron(plus, zero)
    plus_measurement = kron(plus, identity)
    outputs = [channel(controlled(u), input_density) for u in (identity, neg(identity))]
    probs = [trace(mm(plus_measurement, rho)) for rho in outputs]
    assert probs == [1, 0]
    assert mm(x, z) == neg(mm(z, x))
    return {'equal_channel_basis_atoms_checked': len(basis),
            'controlled_identity_plus_outcome_probability': str(probs[0]),
            'controlled_negative_identity_plus_outcome_probability': str(probs[1]),
            'Pauli_orders_equal_as_channels_but_opposite_as_matrices': True,
            'scope': 'exact real matrices; all matrix units span the complex-linear channel domain; no physical implementation claimed'}


def main():
    cases = atoms = coherent = 0
    exhaustive_counts = []
    for n in (2, 3, 4):
        perms = tuple(permutations(range(n)))
        good = total = 0
        for edges in product(perms, repeat=3):
            mismatch, checked = check_cycle(edges, True)
            good += mismatch == 0
            total += 1
            atoms += checked
        assert good == len(perms) ** 2
        exhaustive_counts.append({'labels': n, 'triangles': total, 'coherent_triangles': good})
        cases += total
        coherent += good
    rng = Random(41992)
    general_cycles = 0
    for n, length in product(range(2, 6), range(3, 7)):
        for _ in range(16):
            edges = []
            for __ in range(length):
                edge = list(range(n))
                rng.shuffle(edge)
                edges.append(tuple(edge))
            _, checked = check_cycle(edges, True)
            atoms += checked
            general_cycles += 1
    binary_triangle = ((0, 1), (0, 1), (1, 0))
    mismatch, _ = check_cycle(binary_triangle, True)
    assert mismatch == 2
    source = Path(__file__)
    print(json.dumps({
        'exhaustive_triangles': exhaustive_counts,
        'triangle_settings_checked': cases,
        'coherent_triangle_settings': coherent,
        'sampled_cycle_settings_checked': general_cycles,
        'pointwise_lower_bound_atoms_checked': atoms,
        'binary_inconsistent_triangle_exact_minimax_TV': '1/3',
        'general_mathematical_result': 'For a length-L cycle of permutations on N uniform labels with holonomy defect fraction d, the infimum over joint laws with uniform marginals of maximum edge TV distance is d/L.',
        'independent_checks': 'exact attaining joint laws and exact pointwise dual inequalities; no numerical LP solver',
        'quantum_phase_witness': quantum_witness(),
        'cryptographic_reduction_impossibility_proved': False,
        'all_cycles_require_unbounded_categorical_dimension': False,
        'infinity_category_necessity_proved': False,
        'newness_established': False,
        'Lean_checked': False,
        'source_sha256': {str(source): hashlib.sha256(source.read_bytes()).hexdigest()},
    }, indent=2))


if __name__ == '__main__':
    main()
