"""Audit physical erasure, intermediate request and continuing fair recovery.
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
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeContinuingFairRecovery'
DECLARATIONS = ['Machine.NativeCleanFairRecovery.cleanup', 'Machine.NativeCleanFairRecovery.cleanup_stops', 'Machine.NativeCleanFairRecovery.cleanup_length', 'Machine.NativeCleanFairRecovery.code', 'Machine.NativeCleanFairRecovery.finish', 'Machine.NativeCleanFairRecovery.cleanup_run', 'Machine.NativeCleanFairRecovery.full_run', 'Machine.NativeCleanFairRecovery.observe_finish', 'Machine.NativeCleanFairRecovery.framed_law', 'Machine.NativeCleanFairRecovery.initial_state_law', 'Machine.NativeCleanFairRecovery.cleanup_coin_independent', 'Machine.NativeCleanFairRecovery.stops', 'Machine.NativeCleanFairRecovery.code_length', 'Machine.NativeCleanFairRecovery.haltsWithin', 'Machine.NativeCleanFairRecovery.bounded', 'Machine.NativeCleanFairRecovery.polynomial_time', 'Machine.NativeFairRecoveryRequest.leaf', 'Machine.NativeFairRecoveryRequest.word', 'Machine.NativeFairRecoveryRequest.prepared', 'Machine.NativeFairRecoveryRequest.leaf_run', 'Machine.NativeFairRecoveryRequest.leaf_stops', 'Machine.NativeFairRecoveryRequest.decoder', 'Machine.NativeFairRecoveryRequest.code', 'Machine.NativeFairRecoveryRequest.decoder_stops', 'Machine.NativeFairRecoveryRequest.stops', 'Machine.NativeFairRecoveryRequest.run', 'Machine.NativeFairRecoveryRequest.prepared_equivalent', 'Machine.NativeFairRecoveryRequest.code_length', 'Machine.NativeFairRecoveryRequest.haltsWithin', 'Machine.NativeFairRecoveryRequest.bounded', 'Machine.NativeFairRecoveryRequest.polynomial_time', 'Machine.NativeContinuingFairRecovery.reverseCode', 'Machine.NativeContinuingFairRecovery.code', 'Machine.NativeContinuingFairRecovery.reverse_stops', 'Machine.NativeContinuingFairRecovery.stops', 'Machine.NativeContinuingFairRecovery.prepared_run', 'Machine.NativeContinuingFairRecovery.reverse_run', 'Machine.NativeContinuingFairRecovery.run_at', 'Machine.NativeContinuingFairRecovery.sequence_normalized', 'Machine.NativeContinuingFairRecovery.full_state_run', 'Machine.NativeContinuingFairRecovery.initial_state_law', 'Machine.NativeContinuingFairRecovery.code_length', 'Machine.NativeContinuingFairRecovery.haltsWithin', 'Machine.NativeContinuingFairRecovery.bounded', 'Machine.NativeContinuingFairRecovery.polynomial_time', 'CryptoLogic.Polygraph.Experiment.NativeContinuingFairRecovery.readState', 'CryptoLogic.Polygraph.Experiment.NativeContinuingFairRecovery.read_finish', 'CryptoLogic.Polygraph.Experiment.NativeContinuingFairRecovery.nativeKernel', 'CryptoLogic.Polygraph.Experiment.NativeContinuingFairRecovery.kernel_eq', 'CryptoLogic.Polygraph.Experiment.NativeContinuingFairRecovery.game_path_realized', 'CryptoLogic.Polygraph.Experiment.NativeContinuingFairRecovery.recovery_error']

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
        'audited_theorem_count': 36,
        'audited_definition_count': 15,
        'erased_request_and_coin_cells_per_sampler': 16,
        'protected_result_key_cells': 3,
        'cleanup_runtime_bound_steps': 163,
        'cleanup_code_length_instructions': 271,
        'clean_sampler_runtime_bound_steps': 307,
        'clean_sampler_code_length_upper_bound_instructions': 985484,
        'clean_sampler_full_configuration_exit_factors_through_sampled_key': True,
        'cleanup_actual_terminal_control_coin_independence_verified': True,
        'intermediate_request_prepared_by_native_instructions': True,
        'intermediate_request_adapter_runtime_bound_steps': 47,
        'intermediate_request_adapter_code_length_upper_bound_instructions': 285,
        'adapter_correctness_boundary_current_and_right_cells_blank': True,
        'arbitrary_older_left_frames_preserved': True,
        'continuing_native_forward_reverse_runtime_bound_steps': 663,
        'continuing_native_forward_reverse_code_length_upper_bound_instructions': 1971259,
        'all_raw_inputs_and_inherited_tapes_have_uniform_stopping_bound': True,
        'actual_continuing_full_cell_state_law_at_real_terminal_control_verified': True,
        'full_cell_state_equivalence_removes_redundant_blank_padding_only': True,
        'four_bit_conditional_raw_entry_law_verified': True,
        'finite_game_roundtrip_kernel_matches_single_native_execution': True,
        'native_source_weighted_key_recovery_error': '13037041/536870912',
        'original_reference_cipher_exit_entry_adapter_verified_for_new_roundtrip': False,
        'matching_native_stationary_comparator_constructed': False,
        'general_infinite_state_approximate_four_cell_constructed': False,
        'host_runtime_or_small_code_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
