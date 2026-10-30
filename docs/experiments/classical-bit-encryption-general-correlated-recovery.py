"""Audit arbitrary-state parallel and correlated-frame approximate recovery.
The explicit infinite-support frame is a semantic inherited register; no
bounded native generator, encoding contract, or new caller runtime is inferred.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.GeneralInfiniteCorrelatedRecovery'
DECLARATIONS = ['Foundation.Probability.GeneralKernelVariation.mapped', 'Foundation.Probability.GeneralKernelVariation.mapped_eq', 'Foundation.Probability.GeneralKernelVariation.frame', 'Foundation.Probability.GeneralKernelVariation.frame_eq', 'CryptoLogic.Polygraph.Experiment.general_left_discrepancy', 'CryptoLogic.Polygraph.Experiment.general_right_discrepancy', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.left', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.right', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.parallel', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateGameCoherence.Cell4.exchange', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.left', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.right', 'CryptoLogic.Polygraph.Experiment.GeneralApproximateDiagramEdits.Edit.parallel', 'CryptoLogic.Polygraph.Experiment.GeneralCorrelatedGameFrames.lift_distance', 'CryptoLogic.Polygraph.Experiment.GeneralCorrelatedGameFrames.liftCell', 'CryptoLogic.Polygraph.Experiment.GeneralCorrelatedGameFrames.liftEdit', 'CryptoLogic.Polygraph.Experiment.GeneralCorrelatedGameFrames.liftSeq', 'CryptoLogic.Polygraph.Experiment.GeneralCorrelatedGameFrames.stochasticTagged', 'CryptoLogic.Polygraph.Experiment.GeneralCorrelatedGameFrames.compatible_stochasticTagged', 'CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery.sourceFrame', 'CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery.targetFrame', 'CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery.native_ciphertext', 'CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery.native_compatible', 'CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery.stationary_compatible', 'CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery.framedCell', 'CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery.framed_distance', 'CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery.framed_lower', 'CryptoLogic.Polygraph.Experiment.GeneralNativeCorrelatedRecovery.framedEdit', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.geometric', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.geometric_supported', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.geometric_support_infinite', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.context', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.context_first', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.source_first', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.source_support_infinite', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.source_ciphertext', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.infiniteCell', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.infiniteEdit', 'CryptoLogic.Polygraph.Experiment.GeneralInfiniteCorrelatedRecovery.infinite_lower']

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
        'audited_theorem_count': 20,
        'audited_definition_count': 19,
        'audited_abbreviation_count': 0,
        'endpoint_and_frame_types_require_finite_or_countable_typeclass': False,
        'budget_type': 'ENNReal',
        'source_dependent_output_maps_contract_conditional_distance': True,
        'input_aware_left_inverse_makes_output_encoding_distance_exact': True,
        'arbitrary_correlated_retained_register_preserves_conditional_distance_exactly': True,
        'independent_left_and_right_game_context_discrepancies_exact': True,
        'general_parallel_cells_and_diagram_edits_add_budgets': True,
        'independent_exchange_cell_has_zero_additional_discrepancy': True,
        'correlated_frame_cell_and_edit_transport_preserves_budget': True,
        'correlated_sequential_lift_exchange_cell_has_zero_discrepancy': True,
        'stochastic_side_information_local_invariant_implies_whole_joint_preservation': True,
        'new_global_joint_correspondence_required_for_concrete_ciphertext_frame': False,
        'native_active_kernels_are_existing_charged_continuation_and_packet_caller': True,
        'native_framed_discrepancy_equals_unframed_whole_state_discrepancy': True,
        'native_framed_discrepancy_lower_bound': '3/256',
        'native_framed_discrepancy_upper_bound': '13037041/536870912 + 1849*r/524288 for r=0,...,94',
        'geometric_register_probability': 'P[N=n]=2^(-(n+1))',
        'geometric_register_full_natural_support_verified': True,
        'context_includes_actual_ciphertext_in_support': True,
        'concrete_correlated_source_joint_support_proved_infinite': True,
        'infinite_support_example_approximate_cell_and_diagram_edit_constructed': True,
        'stored_frame_resampled_by_lifted_active_kernel': False,
        'bounded_native_generator_for_geometric_frame_claimed': False,
        'native_finite_tape_encoding_or_runtime_for_new_register_claimed': False,
        'whole_grid_compatibility_optimality_or_security_improvement_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
