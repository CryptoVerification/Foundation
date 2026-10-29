"""Audit numeric observer contraction, native game bounds and sharp witnesses.

This discharges the 37/128 observer bound for adjacent experiments and linked
native callers. Sharp witnesses include a simple private-key-only predicate.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Machine.NativeEightBitKeyWitness'
THEOREMS = ['Foundation.Probability.sum_real_mass', 'Foundation.Probability.centered_weight_bound', 'Foundation.Probability.event_bind_real', 'Foundation.Probability.probabilistic_event_real_bound', 'Foundation.Probability.probabilityGap_eq_ofReal_abs', 'Foundation.Probability.probabilistic_event_bound', 'Foundation.Probability.all_observers_bound', 'Foundation.Probability.finiteVariation_nonneg', 'Foundation.Probability.positive_sum_eq_half_abs', 'Foundation.Probability.event_real_sum', 'Foundation.Probability.positiveTest_real_difference', 'Foundation.Probability.positiveTest_attains', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.tableEightBitLaw_mass', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.table_finiteVariation_eq', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.table_probabilistic_event_edge_bound', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.table_all_observers_edge_bound', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.table_atom_real_count', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.positiveTest_eq_countTest', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.event_real_count', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.keyPair_counts_first', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.keyPair_counts_second', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.keyPair_probability_first', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.keyPair_probability_second', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.keyPair_gap', 'Machine.NativeEightBitObserverSecurity.formatted_edge_bound', 'Machine.NativeEightBitObserverSecurity.initial_edge_bound', 'Machine.NativeEightBitObserverSecurity.toggle_initial_edge_bound', 'Machine.NativeEightBitSharpObservation.observe_equivalent', 'Machine.NativeEightBitSharpObservation.observed_run', 'Machine.NativeEightBitSharpObservation.gap_attained', 'Machine.NativeEightBitSharpObservation.actual_edge_and_gap', 'Machine.NativeEightBitKeyWitness.observe_equivalent', 'Machine.NativeEightBitKeyWitness.observed_run', 'Machine.NativeEightBitKeyWitness.first_acceptance', 'Machine.NativeEightBitKeyWitness.second_acceptance', 'Machine.NativeEightBitKeyWitness.gap_attained']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def local_sources(module):
    pending = [module]
    found = set()
    while pending:
        current = pending.pop()
        path = ROOT / (current.replace('.', '/') + '.lean')
        if path in found:
            continue
        if not path.is_file():
            raise RuntimeError('Missing local dependency: ' + str(path))
        found.add(path)
        for line in path.read_text().splitlines():
            if line.startswith('import '):
                pending.extend(name for name in line.split()[1:] if name.startswith('Foundation.'))
    return sorted(found)


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-native-controlled-cipher-') as directory:
        probe = Path(directory) / 'AxiomProbe.lean'
        probe.write_text('import ' + MODULE + '\n' + ''.join(
            '#print axioms ' + name + '\n' for name in THEOREMS))
        output = run(['lake', 'env', 'lean', str(probe)])
    axioms = {}
    for name in THEOREMS:
        quoted = re.escape("'" + name + "'")
        match = re.search(quoted + r' depends on axioms:\s*\[([^\]]*)\]', output)
        if match:
            axioms[name] = sorted(x.strip() for x in match.group(1).split(',') if x.strip())
        elif re.search(quoted + r' does not depend on any axioms', output):
            axioms[name] = []
        else:
            raise RuntimeError('Missing axiom result for ' + name + ': ' + output)
        if set(axioms[name]) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError('Unexpected axioms for ' + name)
    sources = local_sources(MODULE) + [Path(__file__).resolve()] + [
        ROOT / name for name in ['lakefile.toml', 'lean-toolchain', 'lake-manifest.json']]
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'finite_probabilistic_event_contraction_verified': True,
        'source_observer_bound_premise_discharged_for_all_observers': True,
        'all_actual_grid_edges_verified': True,
        'edge_acceptance_probability_gap_bound': '37/128',
        'native_formatted_state_bound_verified': True,
        'native_raw_initial_bound_verified_for_cell_equivalence_invariant_observers': True,
        'generic_native_caller_requirement': 'same caller and frames; actual all-tape stopping within T',
        'generic_native_combined_runtime_bound': '411+T+1',
        'concrete_native_ciphertext_toggle_combined_runtime_bound': 418,
        'sharp_actual_edge': [[0, 8, 24], [1, 8, 25]],
        'sharp_semantic_probability_gap': '37/128',
        'sharp_exact_integer_count_predicate_verified': True,
        'sharp_simple_key_only_predicate': 'key label equals 0 or 2; ignores ciphertext',
        'sharp_simple_key_only_first_acceptance': '1',
        'sharp_simple_key_only_second_acceptance': '91/128',
        'sharp_gap_attained_after_raw_initial_native_toggle_execution': True,
        'observation_predicates_have_charged_native_implementation_here': False,
        'private_key_observed': True,
        'ordinary_key_hidden_advantage_claimed': False,
        'newness_of_standard_variation_contraction_claimed': False,
        'newness_established': False,
        'infinity_categories_shown_necessary': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
