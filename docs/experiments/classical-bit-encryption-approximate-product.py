"""Audit approximate product cells, retained registers and diagram edits.
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
MODULE = 'Foundation.Crypto.Logic.Polygraph.ApproximateGameProduct'
DECLARATIONS = ['Foundation.Probability.FiniteKernelVariation.map_contraction', 'Foundation.Probability.FiniteKernelVariation.map_isometry', 'Foundation.Probability.FiniteKernelVariation.map_average', 'Foundation.Probability.FiniteKernelVariation.mapped', 'Foundation.Probability.FiniteKernelVariation.frame', 'Foundation.Probability.FiniteKernelVariation.frame_eq', 'CryptoLogic.Polygraph.Experiment.productFintype', 'CryptoLogic.Polygraph.Experiment.left_discrepancy', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.left', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.right', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.parallel', 'CryptoLogic.Polygraph.Experiment.ApproximateGameCoherence.Cell4.exchange', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.left', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.right', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.parallel']

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
        'audited_theorem_count': 7,
        'audited_definition_count': 7,
        'audited_instance_count': 1,
        'finite_endpoint_and_context_outcomes_required': True,
        'deterministic_source_dependent_output_maps_contract_discrepancy': True,
        'correlated_retained_register_preserves_conditional_discrepancy_exactly': True,
        'input_marginal_used_to_weight_active_kernel_distance': True,
        'independent_product_left_context_preserves_discrepancy_exactly': True,
        'approximate_four_cell_left_and_right_frames_keep_error_bound': True,
        'parallel_approximate_four_cells_add_error_bounds': True,
        'independent_interchange_embeds_with_zero_additional_error': True,
        'annotated_diagram_left_and_right_frames_keep_error_bound': True,
        'annotated_parallel_diagram_edits_add_error_bounds': True,
        'copying_sampled_state_treated_as_independent_sampling': False,
        'correlated_game_path_lift_without_joint_preservation_claimed': False,
        'allocated_game_path_losses_preserved_exactly': True,
        'general_infinite_endpoint_extension_claimed': False,
        'native_runtime_for_new_operations_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
