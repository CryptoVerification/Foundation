"""Exact finite four-versus-five key control-table comparison.

The mesh locator and the analytic boundary estimates are explained in the audit.
This executable exhausts finite edges and fair-coin seeds; it does not certify
the entire geometric locator or machine execution in Lean.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, permutations
from math import comb
from pathlib import Path
import hashlib
import json


def x_from_y(y, n):
    return (y[0], y[1]-y[0], y[2]-y[1], n-y[2])


def balanced_counts(raw, bits=8):
    length = sum(map(abs, raw))
    assert length > 0 and sum(raw) == 0
    total = 2**bits
    out = [0]*len(raw)
    for sign in (1, -1):
        group = [i for i, value in enumerate(raw) if sign*value > 0]
        assert sum(abs(raw[i]) for i in group)*2 == length
        counts = {i: total*abs(raw[i])//length for i in group}
        left = total//2-sum(counts.values())
        assert 0 <= left < len(group)
        order = sorted(group, key=lambda i: (-(total*abs(raw[i]) % length), i))
        for i in order[:left]:
            counts[i] += 1
        for i in group:
            out[i] = sign*counts[i]
    assert sum(abs(v) for v in out) == total and sum(out) == 0
    assert sum(v for v in out if v > 0) == total//2
    assert all(abs(a*length-b*total) <= length for a, b in zip(out, raw))
    return tuple(out)


def locator(point, n):
    assert len(point) == 4 and sum(point) == 1 and min(point) >= 0
    y = [point[0], point[0]+point[1], sum(point[:3])]
    base = [min(int(n*v), n-1) for v in y]
    fraction = [n*v-a for v, a in zip(y, base)]
    order = sorted(range(3), key=lambda i: (-fraction[i], -i))
    chain = [tuple(base)]
    current = base[:]
    for i in order:
        current[i] += 1
        chain.append(tuple(current))
    assert all(0 <= a <= b <= c <= n for a, b, c in chain)
    weights = [1-fraction[order[0]], fraction[order[0]]-fraction[order[1]],
               fraction[order[1]]-fraction[order[2]], fraction[order[2]]]
    assert min(weights) >= 0 and sum(weights) == 1
    vertices = [x_from_y(v, n) for v in chain]
    assert all(sum(w*F(v[k], n) for w, v in zip(weights, vertices)) == point[k]
               for k in range(4))
    return vertices, weights


def table_check(n, bits=8):
    vertices = [x_from_y(y, n) for y in combinations_with_replacement(range(n+1), 3)]
    assert len(vertices) == comb(n+3, 3)
    index = {v: i for i, v in enumerate(vertices)}
    edges, cells, faces = set(), set(), Counter()
    for base in combinations_with_replacement(range(n), 3):
        for order in permutations(range(3)):
            current = list(base)
            chain = [tuple(current)]
            for coordinate in order:
                current[coordinate] += 1
                chain.append(tuple(current))
            if not all(a <= b <= c for a, b, c in chain):
                continue
            tet = tuple(index[x_from_y(v, n)] for v in chain)
            assert len(set(tet)) == 4
            assert tet not in cells
            columns = [[vertices[tet[j]][k]-vertices[tet[0]][k]
                        for k in range(3)] for j in range(1, 4)]
            a, b, c = columns
            determinant = (a[0]*(b[1]*c[2]-b[2]*c[1])
                           - a[1]*(b[0]*c[2]-b[2]*c[0])
                           + a[2]*(b[0]*c[1]-b[1]*c[0]))
            assert abs(determinant) == 1
            cells.add(tet)
            edges.update(tuple(sorted(pair)) for pair in combinations(tet, 2))
            faces.update(tuple(sorted(face)) for face in combinations(tet, 3))
    assert len(cells) == n**3
    boundary_faces = 0
    for face, count in faces.items():
        assert count in (1, 2)
        on_boundary = any(all(vertices[v][k] == 0 for v in face) for k in range(4))
        assert on_boundary == (count == 1)
        boundary_faces += count == 1
    assert boundary_faces == 4*n*n
    five, boundary_four = [], {}
    sampler_outcomes = 0
    for i, v in enumerate(vertices):
        minimum = min(v)
        raw = [n-4*a+3*minimum for a in v]+[-12*minimum]
        assert sum(raw) == 0 and sum(map(abs, raw)) >= F(3*n, 2)
        signed = balanced_counts(raw, bits)
        five.append(signed)
        if minimum == 0:
            four = balanced_counts([n-4*a for a in v], bits)
            assert signed == four+(0,)
            boundary_four[i] = four
        # Exhaust every B-bit seed of the bounded sampler at every control vertex.
        seen = [0]*5
        for seed in range(2**bits):
            cutoff = 0
            for key, count in enumerate(signed):
                cutoff += abs(count)
                if seed < cutoff:
                    seen[key] += 1
                    break
            else:
                raise AssertionError('sampler failed to stop')
            sampler_outcomes += 1
        assert seen == list(map(abs, signed))
        for message in (0, 1):
            cipher_counts = [0, 0]
            for count in signed:
                flip = int(count < 0)
                ciphertext = message ^ flip
                assert (ciphertext ^ flip) == message
                cipher_counts[ciphertext] += abs(count)
            assert cipher_counts == [2**(bits-1)]*2
    maximum = 0
    witness = None
    max_parameter = 0
    for i, j in sorted(edges):
        parameter = sum(abs(a-b) for a, b in zip(vertices[i], vertices[j]))
        assert parameter <= 4
        max_parameter = max(max_parameter, parameter)
        jump = sum(abs(a-b) for a, b in zip(five[i], five[j]))
        if jump > maximum:
            maximum, witness = jump, (vertices[i], vertices[j])
    # Every generated cell centroid is located and reconstructed exactly.
    for cell in cells:
        point = [sum(F(vertices[i][k], n) for i in cell)/4 for k in range(4)]
        located, _ = locator(point, n)
        assert tuple(index[v] for v in located) == cell
    beta = F(12, 2**bits)
    assert beta <= F(1, 18)
    boundary_settings = 0
    maximum_boundary_error = F(0)
    for face, count in faces.items():
        if count != 1:
            continue
        point = [sum(F(vertices[i][k], n) for i in face)/3 for k in range(4)]
        local, lam = locator(point, n)
        scales = [F(sum(abs(n-4*a) for a in v), 6*n) for v in local]
        denominator = sum(w*c for w, c in zip(lam, scales))
        assert F(1, 3) <= denominator <= 1
        interpolated = [sum(w*c*F(boundary_four[index[v]][k], 2**bits)
                            for v, w, c in zip(local, lam, scales) if w)
                        /denominator for k in range(4)]
        affine = [F(1, 6)-F(2, 3)*x for x in point]
        ideal = [a/denominator for a in affine]
        assert sum(abs(a-b) for a, b in zip(interpolated, ideal)) <= F(4, 2**bits)
        length = sum(map(abs, interpolated))
        ideal_length = sum(map(abs, ideal))
        assert length > 0 and ideal_length >= F(1, 3)
        target_length = sum(map(abs, affine))
        error = max(abs(a/length-b/target_length) for a, b in zip(interpolated, affine))
        assert error <= beta
        maximum_boundary_error = max(maximum_boundary_error, error)
        boundary_settings += 1
    return {'subdivision_denominator': n, 'key_sampler_fair_coin_bits': bits,
            'vertices': len(vertices), 'tetrahedra': len(cells), 'edges': len(edges),
            'boundary_triangles': boundary_faces, 'boundary_vertices': len(boundary_four),
            'exactly_matching_four_and_five_key_boundary_vertices': len(boundary_four),
            'largest_parameter_edge_l1': str(F(max_parameter, n)),
            'maximum_five_key_joint_TV': str(F(maximum, 2**(bits+1))),
            'maximum_edge_witness_parameter_numerators': witness,
            'enumerated_bounded_sampler_seeds': sampler_outcomes,
            'exactly_checked_cell_centroid_locators': len(cells),
            'projective_boundary_coordinate_error_bound': str(beta),
            'boundary_face_centroids_with_exact_projective_error_checks': boundary_settings,
            'largest_checked_normalized_boundary_coordinate_error': str(maximum_boundary_error),
            'total_tetrahedron_volume_in_first_three_coordinates': '1/6',
            'four_key_required_edge_lower_bound_from_mathematical_argument': '2/3',
            'strict_finite_five_key_edge_gap': F(maximum, 2**(bits+1)) < F(2, 3),
            'four_key_approximate_error_budget_privacy_plus_twice_correctness': '1/8',
            'four_key_approximate_internal_edge_lower_bound': '7/24',
            'strict_five_key_gap_even_against_approximate_four_key_budget':
                F(maximum, 2**(bits+1)) < F(7, 24)}


def main():
    checks = [table_check(n) for n in (8, 16, 32)]
    print(json.dumps({'finite_mesh_checks': checks,
        'mathematical_lower_bound_uses_robust_Brouwer_and_projective_boundary_estimate': True,
        'four_key_interior_assignments_exhaustively_enumerated': False,
        'geometric_mesh_locator_universally_Lean_verified': False,
        'projective_boundary_estimate_Lean_verified': False,
        'Foundation_machine_execution_certified': False,
        'unrestricted_cryptographic_security_separation': False,
        'infinity_categories_shown_necessary': False,
        'newness_established': False,
        'source_sha256': {str(path.resolve()): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [Path(__file__), Path(__file__).resolve().parents[2] /
                'Foundation/Crypto/Semantics/Probability/ClassicalBitRobustBoundary.lean']}}, indent=2))


if __name__ == '__main__':
    main()
