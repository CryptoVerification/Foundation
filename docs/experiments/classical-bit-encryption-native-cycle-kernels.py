"""Audit uniform native contracts for locally edited five-state fair kernels.
The runtime parameter is a fixed compiled sampler, not an uncharged request.
Conditional four-bit inputs are supplied; original-cipher wrappers for the new
family and whole-grid compatibility are not claimed by this audit.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeCycleKernels'
DECLARATIONS = ['Machine.NativeFiveStateSampler.Sampler', 'Machine.NativeFiveStateSampler.kernel', 'Machine.NativeFiveStateSampler.sample_law', 'Machine.NativeFiveStateSampler.request', 'Machine.NativeFiveStateSampler.rawInput', 'Machine.NativeFiveStateSampler.readKey', 'Machine.NativeFiveStateSampler.read_request', 'Machine.NativeFiveStateSampler.payload', 'Machine.NativeFiveStateSampler.leaves', 'Machine.NativeFiveStateSampler.leaves_stops', 'Machine.NativeFiveStateSampler.leaves_length', 'Machine.NativeFiveStateSampler.code', 'Machine.NativeFiveStateSampler.code_def', 'Machine.NativeFiveStateSampler.stops', 'Machine.NativeFiveStateSampler.code_length', 'Machine.NativeFiveStateSampler.entry', 'Machine.NativeFiveStateSampler.finish', 'Machine.NativeFiveStateSampler.leaves_request', 'Machine.NativeFiveStateSampler.full_run', 'Machine.NativeFiveStateSampler.observe_finish', 'Machine.NativeFiveStateSampler.framed_law', 'Machine.NativeFiveStateSampler.entry_equivalent', 'Machine.NativeFiveStateSampler.initial_law', 'Machine.NativeFiveStateSampler.input_length', 'Machine.NativeFiveStateSampler.haltsWithin', 'Machine.NativeFiveStateSampler.bounded', 'Machine.NativeFiveStateSampler.polynomial_time', 'Machine.NativeCleanFiveStateSampler.cleanup', 'Machine.NativeCleanFiveStateSampler.cleanup_stops', 'Machine.NativeCleanFiveStateSampler.cleanup_length', 'Machine.NativeCleanFiveStateSampler.code', 'Machine.NativeCleanFiveStateSampler.finish', 'Machine.NativeCleanFiveStateSampler.cleanup_run', 'Machine.NativeCleanFiveStateSampler.full_run', 'Machine.NativeCleanFiveStateSampler.observe_finish', 'Machine.NativeCleanFiveStateSampler.framed_law', 'Machine.NativeCleanFiveStateSampler.initial_state_law', 'Machine.NativeCleanFiveStateSampler.cleanup_coin_independent', 'Machine.NativeCleanFiveStateSampler.stops', 'Machine.NativeCleanFiveStateSampler.code_length', 'Machine.NativeCleanFiveStateSampler.haltsWithin', 'Machine.NativeCleanFiveStateSampler.bounded', 'Machine.NativeCleanFiveStateSampler.polynomial_time', 'Machine.NativeContinuingFiveStateSampler.nextCode', 'Machine.NativeContinuingFiveStateSampler.code', 'Machine.NativeContinuingFiveStateSampler.next_stops', 'Machine.NativeContinuingFiveStateSampler.stops', 'Machine.NativeContinuingFiveStateSampler.prepared_run', 'Machine.NativeContinuingFiveStateSampler.next_run', 'Machine.NativeContinuingFiveStateSampler.run_at', 'Machine.NativeContinuingFiveStateSampler.full_state_run', 'Machine.NativeContinuingFiveStateSampler.initial_state_law', 'Machine.NativeContinuingFiveStateSampler.code_length', 'Machine.NativeContinuingFiveStateSampler.haltsWithin', 'Machine.NativeContinuingFiveStateSampler.bounded', 'Machine.NativeContinuingFiveStateSampler.polynomial_time', 'Machine.NativeCertifiedFiveStateKernel.draw', 'Machine.NativeCertifiedFiveStateKernel.draw_law', 'Machine.NativeCertifiedFiveStateKernel.kernel_eq', 'Machine.NativeCertifiedFiveStateKernel.code', 'Machine.NativeCertifiedFiveStateKernel.stops', 'Machine.NativeCertifiedFiveStateKernel.code_length', 'Machine.NativeCertifiedFiveStateKernel.full_run', 'Machine.NativeCertifiedFiveStateKernel.initial_law', 'Machine.NativeCertifiedFiveStateKernel.initial_state_law', 'Machine.NativeCertifiedFiveStateKernel.bounded', 'Machine.NativeCertifiedFiveStateKernel.polynomial_time', 'Machine.NativeCertifiedFiveStateKernel.pathCode', 'Machine.NativeCertifiedFiveStateKernel.path_stops', 'Machine.NativeCertifiedFiveStateKernel.path_length', 'Machine.NativeCertifiedFiveStateKernel.path_polynomial_time', 'Machine.NativeCertifiedFiveStateKernel.path_joint_law', 'Machine.NativeCertifiedFiveStateKernel.path_joint_state_law', 'Machine.NativeCycleKernelSampler.draw', 'Machine.NativeCycleKernelSampler.draw_law', 'Machine.NativeCycleKernelSampler.kernel_eq', 'Machine.NativeCycleKernelSampler.cleanCode', 'Machine.NativeCycleKernelSampler.clean_stops', 'Machine.NativeCycleKernelSampler.clean_length', 'Machine.NativeCycleKernelSampler.clean_full_run', 'Machine.NativeCycleKernelSampler.clean_initial_state_law', 'Machine.NativeCycleKernelSampler.clean_initial_law', 'Machine.NativeCycleKernelSampler.clean_joint_observed', 'Machine.NativeCycleKernelSampler.clean_joint_state_law', 'Machine.NativeCycleKernelSampler.loopCode', 'Machine.NativeCycleKernelSampler.reverse_kernel', 'Machine.NativeCycleKernelSampler.loop_stops', 'Machine.NativeCycleKernelSampler.loop_length', 'Machine.NativeCycleKernelSampler.loop_initial_state_law', 'Machine.NativeCycleKernelSampler.loop_ciphertext', 'Machine.NativeCycleKernelSampler.loop_joint_preserves', 'Machine.NativeCycleKernelSampler.loop_joint_state_law', 'Machine.NativeCycleKernelSampler.cleanBounded', 'Machine.NativeCycleKernelSampler.loopBounded', 'Machine.NativeCycleKernelSampler.clean_polynomial_time', 'Machine.NativeCycleKernelSampler.loop_polynomial_time', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.cleanKernel', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.clean_kernel_eq', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.loopKernel', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.loop_kernel_eq', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.clean_preserves', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.loop_preserves', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.clean_discrepancy', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.loop_perturbation', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.seed_recovery_distance', 'CryptoLogic.Polygraph.Experiment.NativeCycleKernels.loop_recovery_bound']

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
        'audited_theorem_count': 77,
        'audited_definition_count': 26,
        'audited_abbreviation_count': 3,
        'generic_five_state_twelve_bit_sampler_native_contract_verified': True,
        'generic_four_bit_request_length': 4,
        'generic_raw_sampler_runtime_bound_steps': 143,
        'generic_raw_sampler_code_length_upper_bound_instructions': 985210,
        'generic_clean_sampler_runtime_bound_steps': 307,
        'generic_clean_sampler_code_length_upper_bound_instructions': 985484,
        'generic_clean_sampler_erased_request_and_random_cells': 16,
        'generic_clean_sampler_inherited_tape_frames_retained': True,
        'generic_cleanup_coins_independent_conditional_on_sampled_key': True,
        'generic_two_stage_sampler_with_charged_adapter_runtime_bound_steps': 663,
        'generic_two_stage_code_length_upper_bound_instructions': 1971259,
        'generic_two_stage_actual_terminal_control_full_cell_state_law_verified': True,
        'generic_certified_integer_table_compiled_to_clean_native_program': True,
        'generic_local_edit_path_joint_observed_and_full_cell_state_laws_verified': True,
        'generic_native_local_edit_path_retained_label_type': 'Bool',
        'generic_native_contracts_support_arbitrary_key_counts_or_coin_widths': False,
        'five_state_family_size': 95,
        'five_state_family_clean_joint_key_ciphertext_native_laws_verified': True,
        'five_state_family_conditional_clean_distance_from_seed': '1849*r/524288 for r=0,...,94',
        'five_state_family_native_loop_recovery_error_upper_bound': '13037041/536870912 + 1849*r/524288 for r=0,...,94',
        'five_state_family_two_stage_actual_native_kernel_realized': True,
        'five_state_family_loop_joint_key_ciphertext_full_cell_law_verified': True,
        'uniform_stopping_on_all_raw_inputs_and_tapes': True,
        'each_family_parameter_selects_a_fixed_compiled_program': True,
        'new_family_original_cipher_entry_and_packet_restore_wrappers_verified': False,
        'new_family_matching_stationary_native_comparator_verified': False,
        'new_family_exact_optimal_recovery_error_or_security_improvement_claimed': False,
        'whole_grid_compatibility_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
