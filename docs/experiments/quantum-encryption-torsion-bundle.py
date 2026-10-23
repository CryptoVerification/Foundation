"""An explicit rational suspended-Hopf clutch and the general seven-key compiler.

The nonzero homotopy class comes from Hatcher, Corollary 4J.4, not from finite
tests. This program checks its representative, the resulting ground projector,
and chart identities. It does not compute homotopy, Chern classes, or sections.
Earlier archived sources remain unchanged.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import importlib.util
import json

DEPENDENCY = Path(__file__).with_name('quantum-encryption-yang-bundle.py')
spec = importlib.util.spec_from_file_location('frozen_yang_bundle', DEPENDENCY)
b = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)


def suspended_hopf(a, z):
    """Smooth S4 -> S3; z is a quaternion and a*a+|z|^2=1."""
    assert a*a+sum(x*x for x in z) == 1
    imaginary = b.qm(b.qm(z, [0, 1, 0, 0]), b.conjugate(z))
    assert imaginary[0] == 0
    denominator = 1+a*a
    return [2*a/denominator]+[x/denominator for x in imaginary[1:]]


def compile_clutched(t, s, direction, clutch):
    """Compile a point of a suspension using a specified unit-quaternion clutch."""
    q = clutch(*direction)
    return b.compile_point(t, s, q)


def checks():
    directions = []
    for v in product(range(-1, 2), repeat=3):
        length = sum(x*x for x in v)
        directions.append([F(1-length, 1+length)]+[F(2*x, 1+length) for x in v])
    latitudes = [(F(1), F(0)), (F(3, 5), F(4, 5)), (F(0), F(1)),
                 (-F(3, 5), F(4, 5)), (-F(1), F(0))]
    representatives = transitions = gates = 0
    for index, (q, (a, radius)) in enumerate(product(directions, latitudes)):
        z = [radius*x for x in q]
        clutch = suspended_hopf(a, z)
        assert sum(x*x for x in clutch) == 1
        assert suspended_hopf(a, [-x for x in z]) == clutch
        hopf = b.qm(b.qm(q, [0, 1, 0, 0]), b.conjugate(q))
        expected = [2*a/(1+a*a)]+[radius*radius*x/(1+a*a) for x in hopf[1:]]
        assert clutch == expected
        assert (2*a/(1+a*a))**2+((1-a*a)/(1+a*a))**2 == 1
        t, s = latitudes[1+index % 3]
        h, projector, north, south = b.data(t, s, clutch)
        assert b.p.mm(projector, projector) == projector and b.trace(projector) == 4
        assert b.p.mm(h, h) == b.I8
        assert south == b.scale(b.p.mm(north, b.left(clutch)), s/(1+t))
        transitions += 1
        weights, operators = compile_clutched(t, s, (a, z), suspended_hopf)
        assert sum(weights) == 1 and min(weights) >= 0
        for w, op in zip(weights, operators):
            if w:
                assert b.p.mm(b.p.tr(op), op) == b.I8
                assert b.p.mm(op, projector) == b.p.mm(projector, op)
                gates += 1
        representatives += 1
    pole_checks = 0
    for t in (F(-1), F(1)):
        reference = None
        for q in directions:
            # Different inner points all represent the same outer pole.
            weights, ops = compile_clutched(t, F(0), (F(0), q), suspended_hopf)
            positive = [(w, op) for w, op in zip(weights, ops) if w]
            if reference is None:
                reference = positive
            assert positive == reference
            pole_checks += 1
    # A constant clutch has coincident north/south Pauli channels. It supplies
    # a concrete four-key comparator, with the same physical/logical dimensions.
    trivial_comparators = 0
    for t, s in latitudes[1:-1]:
        _, projector, north, south = b.data(t, s, [1, 0, 0, 0])
        assert b.local_gates(north, 2*(1+t), projector) == b.local_gates(south, 2*(1-t), projector)
        trivial_comparators += 1
    return {'rational_clutch_representatives_checked': representatives,
            'ground_projector_and_chart_transition_checks': transitions,
            'positive_probability_unitary_branch_checks': gates,
            'pole_independence_checks': pole_checks,
            'constant_clutch_four_key_comparators': trivial_comparators,
            'clutch_formula': '(2a, z i conjugate(z)) / (1+a^2)',
            'physical_complex_dimension': 4, 'logical_complex_dimension': 2}


def main():
    result = {'exact_rational_checks': checks(),
              'mathematical_classification': 'A continuous perfect four-key qubit encryption family exists exactly when the oriented traceless-Hermitian endomorphism bundle reduces to the ordered-axis sign group D2. On a simply connected CW base this is equivalent to triviality of that real rank-three bundle.',
              'torsion_example_mathematical_claim': 'The suspended-Hopf clutch yields a nontrivial rank-two bundle on S5 with c1=c2=0, no perfect continuous four-key code-preserving encryption, and a seven-key construction.',
              'arbitrarily_high_obstruction_claim': 'For every fixed Postnikov truncation degree, some sphere-parametrized family has the same truncated SU2 bundle-classifying data as a trivial family but different feasibility of perfect continuous four-key encryption.',
              'robust_four_key_bound': 'Every nontrivial SU2 clutch over S^(r+1), r>=2, forces some privacy + (5/2) maximum positive-key recovery error >=1/4 in a continuous four-key code-preserving family.',
              'topological_classification_or_torsion_computer_verified': False,
              'five_or_six_key_nonexistence_for_torsion_example_claimed': False,
              'higher_parameter_models_experimentally_realized': False,
              'infinity_categorical_formalism_proved_indispensable': False,
              'Lean_checked': False, 'newness_established': False,
              'source_sha256': {str(f.resolve()): hashlib.sha256(f.read_bytes()).hexdigest()
                                for f in (Path(__file__), DEPENDENCY, b.DEPENDENCY)}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
