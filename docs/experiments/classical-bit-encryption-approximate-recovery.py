"""Audit approximate finite game four-cells, pasting, and recovery example.

Discrepancy is source-weighted conditional total variation. Allocated path
losses stay equal. Common preserving contexts contract discrepancy. The zero
case yields equality on source support; returning a strict cell additionally
requires full source support. Semantic comparison gives no native runtime.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.ApproximateRecovery'
DECLARATIONS = ['Foundation.Probability.FiniteKernelVariation.singleton', 'Foundation.Probability.FiniteKernelVariation.variation_nonneg', 'Foundation.Probability.FiniteKernelVariation.variation_self', 'Foundation.Probability.FiniteKernelVariation.variation_symm', 'Foundation.Probability.FiniteKernelVariation.variation_triangle', 'Foundation.Probability.FiniteKernelVariation.variation_zero_iff', 'Foundation.Probability.FiniteKernelVariation.variation_pure', 'Foundation.Probability.FiniteKernelVariation.bind_real', 'Foundation.Probability.FiniteKernelVariation.distance', 'Foundation.Probability.FiniteKernelVariation.nonneg', 'Foundation.Probability.FiniteKernelVariation.self', 'Foundation.Probability.FiniteKernelVariation.symm', 'Foundation.Probability.FiniteKernelVariation.triangle', 'Foundation.Probability.FiniteKernelVariation.zero_on_support', 'Foundation.Probability.FiniteKernelVariation.mixture', 'Foundation.Probability.FiniteKernelVariation.postprocess', 'Foundation.Probability.FiniteKernelVariation.post', 'Foundation.Probability.FiniteKernelVariation.pre', 'Foundation.Probability.FiniteKernelVariation.seq', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Comparison.ofExact', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.sound', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.nonneg', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.pre', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.post', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.contextual', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.strictOfZero', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.retained_observer_bound', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.joint_observer_bound', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.joint_probability_gap', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.sourceFintype', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.targetFintype', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.nativeSourceFintype', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.stationaryStep', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.stationary', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.discrepancy_is_error', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.example_discrepancy', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.recoveryCell', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.example_minimal_tolerance', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.required_tolerance', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.no_zero_cell', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.contextual', 'CryptoLogic.Polygraph.Experiment.ApproximateRecovery.exactNativeAsApprox', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Comparison', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Comparison.mk', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Comparison.kernel_bound', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Comparison.loss_eq', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.generator', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.exact', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.refl', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.symm', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.trans', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.weaken', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.seq', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.rec']
THEOREM_COUNT = 29
DEFINITION_COUNT = 10
INSTANCE_COUNT = 3
SUPPORT_DECLARATION_COUNT = 13

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
        'audited_instance_count': INSTANCE_COUNT,
        'audited_support_declaration_count': SUPPORT_DECLARATION_COUNT,
        'finite_endpoint_outcomes_required': True,
        'discrepancy': 'source-weighted conditional total variation',
        'pointwise_equality_on_unreachable_states_claimed': False,
        'allocated_game_path_losses_preserved_exactly': True,
        'proof_relevant_approximate_four_cell_data_verified': True,
        'vertical_pasting_adds_discrepancies': True,
        'sequential_pasting_adds_discrepancies': True,
        'common_preserving_prefix_contracts_discrepancy': True,
        'common_suffix_contracts_discrepancy': True,
        'two_sided_common_context_preserves_bound': True,
        'retained_input_and_final_state_probabilistic_observers_bounded': True,
        'observer_output_type_required_finite': False,
        'strict_four_cells_embed_at_zero': True,
        'zero_discrepancy_implies_kernel_equality_on_source_support': True,
        'return_to_strict_four_cell_requires_full_source_support': True,
        'preserving_recovery_example_discrepancy': '5719/253440',
        'chosen_example_minimum_comparison_tolerance_verified': True,
        'all_recovery_paths_minimum_tolerance_at_least': '3/256',
        'recovery_example_allocated_roundtrip_and_stationary_loss': '3/128',
        'existing_native_two_to_five_recovery_cell_embedded_at_zero': True,
        'positive_error_example_or_arbitrary_context_given_native_runtime': False,
        'general_infinite_endpoint_outcome_extension_claimed': False,
        'ordinary_strict_diagram_edits_created_for_positive_discrepancy': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
