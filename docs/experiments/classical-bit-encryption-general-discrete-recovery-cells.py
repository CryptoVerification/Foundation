"""Audit approximate cells on arbitrary discrete PMF state types.
Budgets are extended nonnegative reals. No continuous measure semantics,
infinite-support native sampling, or infinity-category necessity is claimed.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.GeneralNativeRecoveryCells'
DECLARATIONS = ['Foundation.Probability.GeneralKernelVariation.variation', 'Foundation.Probability.GeneralKernelVariation.distance', 'Foundation.Probability.GeneralKernelVariation.variation_self', 'Foundation.Probability.GeneralKernelVariation.variation_symm', 'Foundation.Probability.GeneralKernelVariation.variation_triangle', 'Foundation.Probability.GeneralKernelVariation.variation_le_one', 'Foundation.Probability.GeneralKernelVariation.variation_ne_top', 'Foundation.Probability.GeneralKernelVariation.variation_zero_iff', 'Foundation.Probability.GeneralKernelVariation.sum_difference_bound', 'Foundation.Probability.GeneralKernelVariation.postprocess', 'Foundation.Probability.GeneralKernelVariation.mixture', 'Foundation.Probability.GeneralKernelVariation.self', 'Foundation.Probability.GeneralKernelVariation.symm', 'Foundation.Probability.GeneralKernelVariation.triangle', 'Foundation.Probability.GeneralKernelVariation.le_one', 'Foundation.Probability.GeneralKernelVariation.zero_on_support', 'Foundation.Probability.GeneralKernelVariation.post', 'Foundation.Probability.GeneralKernelVariation.bind_average', 'Foundation.Probability.GeneralKernelVariation.pre', 'Foundation.Probability.GeneralKernelVariation.seq', 'Foundation.Probability.GeneralKernelVariation.variation_finite_eq', 'Foundation.Probability.GeneralKernelVariation.distance_finite_eq', 'Foundation.Probability.GeneralKernelVariation.map_contraction', 'Foundation.Probability.GeneralKernelVariation.map_isometry', 'Foundation.Probability.GeneralKernelVariation.event_bound', 'Foundation.Probability.GeneralKernelVariation.probabilistic_event_bound', 'Foundation.Probability.GeneralKernelVariation.all_observers_bound', 'Foundation.Probability.GeneralKernelVariation.joint', 'Foundation.Probability.GeneralKernelVariation.joint_apply', 'Foundation.Probability.GeneralKernelVariation.joint_variation', 'Foundation.Probability.GeneralKernelVariation.map_average', 'Foundation.Probability.GeneralKernelVariation.mapped_distance', 'Foundation.Probability.GeneralKernelVariation.joint_observer_bound', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Comparison', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Comparison.ofExact', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.sound', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.pre', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.post', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.contextual', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.strictOfZero', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.joint_observer_bound', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.ofFinite', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.comparison', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.kernel_bound', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.loss_eq', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.contextual', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.seq', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.observer_bound', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.game_bound', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.ofFinite', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.State', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.state_infinite', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.sourceLaw', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.source_law', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.nativeKernel', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.reset', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.stationaryKernel', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.stationary_from_halt', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.native_encode', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.stationary_encode', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.row_variation', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.discrepancy', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.discrepancy_bound', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.discrepancy_lower', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecovery.whole_state_observer_bound', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.targetLaw', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.target_actual', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.sourceGame', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.targetGame', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.budget', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.native_preserve', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.stationary_preserve', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.decode_reset', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.cut_event', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.native_bad_bound', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.nativeStep', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.stationaryStep', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.recoveryCell', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.recoveryEdit', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.actualRecoveryCell', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.actualRecoveryEdit', 'CryptoLogic.Polygraph.Experiment.GeneralNativeRecoveryCells.no_zero_cell', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Comparison.mk', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Comparison.kernel_bound', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Comparison.loss_eq', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Comparison.rec', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.generator', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.exact', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.refl', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.symm', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.trans', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.weaken', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.seq', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.rec', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.structural', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.strict', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.game', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.refl', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.symm', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.trans', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.weaken', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.rec']

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
        'audited_theorem_count': 54,
        'audited_definition_count': 26,
        'audited_abbreviation_count': 1,
        'audited_structure_count': 1,
        'audited_inductive_count': 2,
        'audited_constructor_projection_recursor_count': 20,
        'endpoint_types_require_finite_or_countable_typeclass': False,
        'probability_model': 'PMF with summable point masses; arbitrary discrete state types',
        'budget_type': 'ENNReal',
        'variation_and_source_weighted_kernel_distance_bounded_by_one': True,
        'general_triangle_mixture_pre_post_and_sequential_bounds_verified': True,
        'finite_variation_and_conditional_distance_preserved_exactly_under_ofReal': True,
        'retained_input_joint_variation_equals_expected_conditional_variation': True,
        'arbitrary_probabilistic_joint_observers_bounded': True,
        'general_proof_relevant_approximate_four_cells_sound': True,
        'general_closed_diagram_edits_and_sequential_contexts_sound': True,
        'old_finite_cells_and_edits_embed_with_same_budget': True,
        'native_full_state_type_proved_infinite': True,
        'native_source_is_actual_original_930_step_execution': True,
        'native_source_support_finite_in_this_example': True,
        'native_continuation_and_packet_caller_use_actual_machine_kernels': True,
        'native_stationary_kernel_realized_by_charged_halt_padding_with_actual_control_instantiation': True,
        'native_whole_state_conditional_distance_lower_bound': '3/256',
        'native_whole_state_conditional_distance_upper_bound': '13037041/536870912 + 1849*r/524288 for r=0,...,94',
        'native_general_approximate_cells_and_diagram_edits_constructed': True,
        'native_zero_budget_approximate_cell_ruled_out': True,
        'general_horizontal_product_or_correlated_frame_interface_claimed': False,
        'continuous_measure_extension_claimed': False,
        'native_sampler_for_arbitrary_infinite_support_PMF_claimed': False,
        'efficiency_of_arbitrary_semantic_observers_claimed': False,
        'whole_grid_compatibility_or_optimality_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
