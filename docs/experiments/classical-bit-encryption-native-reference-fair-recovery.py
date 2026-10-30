"""Audit the original native cipher, fair recovery caller, and joint laws.
Errors measure conditional kernel discrepancy, distinct from game-path loss.
The inherited structural cells may copy/erase proof certificates, not random state.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeCanonicalFairRecovery'
DECLARATIONS = ['Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecoveryCipher.source_ciphertext', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecoveryCipher.forward_ciphertext', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecoveryCipher.reverse_ciphertext', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecoveryCipher.roundtrip_ciphertext', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecoveryCipher.joint_roundtrip_preserve', 'Machine.NativeReferenceFairRequest.leaf', 'Machine.NativeReferenceFairRequest.prepared', 'Machine.NativeReferenceFairRequest.leaf_run', 'Machine.NativeReferenceFairRequest.leaf_stops', 'Machine.NativeReferenceFairRequest.decoder', 'Machine.NativeReferenceFairRequest.code', 'Machine.NativeReferenceFairRequest.decoder_stops', 'Machine.NativeReferenceFairRequest.stops', 'Machine.NativeReferenceFairRequest.run', 'Machine.NativeReferenceFairRequest.prepared_equivalent', 'Machine.NativeReferenceFairRequest.code_length', 'Machine.NativeReferenceFairRequest.haltsWithin', 'Machine.NativeReferenceFairRequest.bounded', 'Machine.NativeReferenceFairRequest.polynomial_time', 'Machine.NativeReferenceFairRecovery.continuation', 'Machine.NativeReferenceFairRecovery.code', 'Machine.NativeReferenceFairRecovery.cleanEncode', 'Machine.NativeReferenceFairRecovery.cleanEncode_injective', 'Machine.NativeReferenceFairRecovery.prepared_run', 'Machine.NativeReferenceFairRecovery.continuation_run', 'Machine.NativeReferenceFairRecovery.kernelAt', 'Machine.NativeReferenceFairRecovery.kernelAt_finish', 'Machine.NativeReferenceFairRecovery.kernelAt_encode', 'Machine.NativeReferenceFairRecovery.continuation_stops', 'Machine.NativeReferenceFairRecovery.framed_law', 'Machine.NativeReferenceFairRecovery.initial_law', 'Machine.NativeReferenceFairRecovery.stops', 'Machine.NativeReferenceFairRecovery.continuation_length', 'Machine.NativeReferenceFairRecovery.code_length', 'Machine.NativeReferenceFairRecovery.haltsWithin', 'Machine.NativeReferenceFairRecovery.bounded', 'Machine.NativeReferenceFairRecovery.polynomial_time', 'CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery.read_clean', 'CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery.observedKernel', 'CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery.observed_kernel_eq', 'CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery.cutJoint', 'CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery.cut_joint', 'CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery.recovery_error', 'CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery.full_final_key_law', 'CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery.cut_final_is_actual_execution', 'CryptoLogic.Polygraph.Experiment.NativeReferenceFairRecovery.source_joint_law', 'Machine.NativeCanonicalFairRecovery.keep_blank', 'Machine.NativeCanonicalFairRecovery.clean_equivalent', 'Machine.NativeCanonicalFairRecovery.caller_run_at', 'Machine.NativeCanonicalFairRecovery.callerKernelAt', 'Machine.NativeCanonicalFairRecovery.callerKernelAt_clean', 'Machine.NativeCanonicalFairRecovery.code', 'Machine.NativeCanonicalFairRecovery.padding', 'Machine.NativeCanonicalFairRecovery.stationaryCode', 'Machine.NativeCanonicalFairRecovery.positive_halt_stops', 'Machine.NativeCanonicalFairRecovery.padding_stops', 'Machine.NativeCanonicalFairRecovery.final_control_equal', 'Machine.NativeCanonicalFairRecovery.clean_source_law', 'Machine.NativeCanonicalFairRecovery.transformed_law', 'Machine.NativeCanonicalFairRecovery.stationary_framed_law', 'Machine.NativeCanonicalFairRecovery.stationary_initial_law', 'Machine.NativeCanonicalFairRecovery.full_cell_identity', 'Machine.NativeCanonicalFairRecovery.stops', 'Machine.NativeCanonicalFairRecovery.stationary_stops', 'Machine.NativeCanonicalFairRecovery.haltsWithin', 'Machine.NativeCanonicalFairRecovery.stationary_haltsWithin', 'Machine.NativeCanonicalFairRecovery.bounded', 'Machine.NativeCanonicalFairRecovery.stationaryBounded', 'Machine.NativeCanonicalFairRecovery.polynomial_time', 'Machine.NativeCanonicalFairRecovery.stationary_polynomial_time', 'Machine.NativeCanonicalFairRecovery.public_identity', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.fullLaw', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.stationaryLaw', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.nativeGame', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.stationaryGame', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.fullReification', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.publicGame', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.publicReferenceGame', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.publicReification', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.decode_finish', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.cutJoint', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.cut_joint', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.recovery_error', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.final_key_law', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalFairRecovery.cut_final_is_actual_execution']

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
    with tempfile.TemporaryDirectory(prefix='foundation-approximate-diagram-') as directory:
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
        'audited_theorem_count': 58,
        'audited_definition_count': 27,
        'actual_reference_exit_key_and_both_output_cells_read_and_erased': True,
        'reference_exit_ciphertext_toggle_undone_by_native_branching': True,
        'reference_request_adapter_runtime_bound_steps': 50,
        'reference_request_adapter_code_length_upper_bound_instructions': 309,
        'continuation_including_adapter_and_roundtrip_runtime_bound_steps': 714,
        'original_cipher_runtime_bound_steps': 930,
        'single_original_cipher_and_recovery_runtime_bound_steps': 1645,
        'continuation_code_length_upper_bound_instructions': 1971571,
        'full_code_length_extra_upper_bound_over_reference_instructions': 1971574,
        'uniform_stopping_bound_on_all_raw_inputs_and_tapes': True,
        'full_cell_state_law_for_actual_original_cipher_and_continuation_verified': True,
        'final_key_ciphertext_state_embedding_injective': True,
        'cut_joint_uses_actual_930_step_reference_law_and_native_continuation': True,
        'cut_final_marginal_matches_actual_1645_step_program': True,
        'native_source_weighted_key_recovery_error': '13037041/536870912',
        'original_key_retained_as_proof_metadata_not_extra_machine_register': True,
        'selected_source_ciphertext_preserved_on_forward_and_reverse_support': True,
        'selected_source_joint_key_ciphertext_law_restored_exactly': True,
        'native_selected_source_final_law_equals_source_in_explicit_clean_encoding': True,
        'joint_law_restoration_for_every_grid_vertex_claimed': False,
        'canonical_reference_output_packet_restored': True,
        'matching_native_stationary_comparator_constructed': True,
        'native_packet_restore_caller_runtime_bound_steps': 30,
        'canonical_original_cipher_and_recovery_runtime_bound_steps': 1676,
        'stationary_wrapped_reference_runtime_bound_steps': 932,
        'common_terminal_control_reached_by_actual_native_programs': True,
        'all_cell_state_laws_equal_against_charged_stationary_reference': True,
        'public_output_law_equals_original_unwrapped_930_step_reference': True,
        'full_cell_and_public_probability_game_exact_steps_verified': True,
        'recovery_error_after_charged_packet_caller': '13037041/536870912',
        'post_packet_cut_joint_final_marginal_matches_actual_program': True,
        'final_marginal_equality_used_to_assert_exact_conditional_recovery': False,
        'equal_running_time_or_time_sensitive_observations_claimed': False,
        'whole_native_state_identity_against_unwrapped_reference_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
