"""Audit quantitative conditional recovery error on the five-state edge.

The error averages source-state mismatch over the original source law. It is
not a gap between final marginal laws or a public cryptographic advantage.
The sharp unconstrained reverse witness does not preserve the reverse marginal;
a separate preserving pair has a certified larger error, not an optimality claim.
No native runtime is assigned to the semantic maximal conditional kernels.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.QuantitativeRecovery'
DECLARATIONS = ['Foundation.Probability.FiniteRecoveryError.capacity', 'Foundation.Probability.FiniteRecoveryError.deterministic_dominates', 'Foundation.Probability.FiniteRecoveryError.deterministic_capacity', 'Foundation.Probability.FiniteRecoveryError.matrix_success_bound', 'Foundation.Probability.FiniteRecoveryError.singleton', 'Foundation.Probability.FiniteRecoveryError.bind_real', 'Foundation.Probability.FiniteRecoveryError.failure', 'Foundation.Probability.FiniteRecoveryError.different_probability', 'Foundation.Probability.FiniteRecoveryError.failure_eq_one_sub_success', 'Foundation.Probability.FiniteRecoveryError.failure_lower', 'Foundation.Probability.FiniteRecoveryError.failure_identity_joint', 'Foundation.Probability.ApproximateRecoveryTransport.induced_roundtrip', 'Foundation.Probability.ApproximateRecoveryTransport.induced_failure_le', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.sourceCounts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.targetCounts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.assignedCounts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.retainedCounts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.decoder_certificate', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.all_decoder_counts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.identity_counts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.source_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.target_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.capacity_eq', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.capacity_bound', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.recovery_error_lower', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.variation', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.attainingForward', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.attaining_preserve', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.attaining_error', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.attaining_reverse_not_preserve', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.preservingReverse', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.reverse_preserves', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.maximal_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.forward_matrix', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.reverse_matrix', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError.preserving_error', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.pathError', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.path_error_lower', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.required_tolerance', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.stateError', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.state_error_lower', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.exampleForward', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.exampleReverse', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.exampleRoundtrip', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.example_error', 'CryptoLogic.Polygraph.Experiment.QuantitativeRecovery.example_loss']
THEOREM_COUNT = 33
DEFINITION_COUNT = 13

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
            '#print axioms ' + name + '\n' for name in DECLARATIONS))
        output = run(['lake', 'env', 'lean', str(probe)])
    axioms = {}
    for name in DECLARATIONS:
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
        'axioms_per_declaration': axioms,
        'sorry_or_additional_axioms_in_listed_declarations': False,
        'audited_theorem_count': THEOREM_COUNT,
        'audited_definition_count': DEFINITION_COUNT,
        'grid_source_vertex': [1, 2, 3],
        'grid_target_vertex': [1, 2, 4],
        'source_atom_counts': [43, 43, 42, 111, 17],
        'target_atom_counts': [45, 44, 39, 111, 17],
        'denominator': 256,
        'deterministic_decoder_certificate_cardinality': 3125,
        'retained_integer_mass_upper_bound': 253,
        'randomized_reverse_dominated_by_some_deterministic_decoder': True,
        'uniform_average_recovery_error_lower_bound': '3/256',
        'forward_marginal_preservation_required_for_lower_bound': True,
        'reverse_marginal_preservation_required_for_lower_bound': False,
        'unconstrained_reverse_lower_bound_attained': True,
        'unconstrained_attaining_reverse_does_not_preserve_source_marginal': True,
        'separate_pair_preserves_both_endpoint_marginals': True,
        'both_preserving_candidate_recovery_error': '5719/253440',
        'both_preserving_optimal_error_proved': False,
        'preserving_example_constructed_as_actual_game_paths': True,
        'preserving_game_roundtrip_allocated_loss': '3/128',
        'full_forward_and_reverse_transition_tables_verified': True,
        'arbitrary_game_path_recovery_error_lower_bound_verified': True,
        'required_approximate_kernel_recovery_tolerance_at_least': '3/256',
        'arbitrary_full_cell_state_recovery_error_lower_bound_verified': True,
        'outside_source_view_return_states_allowed': True,
        'error_is_source_weighted_conditional_return_mismatch': True,
        'error_claimed_as_final_marginal_distance_or_public_advantage': False,
        'attaining_and_preserving_kernels_have_native_runtime_contract': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
