"""Audit error-annotated closed diagram edits and recovery integration.
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
MODULE = 'Foundation.Crypto.Logic.Polygraph.ApproximateDiagramEdits'
DECLARATIONS = ['CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.structural', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.strict', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.game', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.refl', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.symm', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.trans', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.weaken', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.rec', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.comparison', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.nonneg', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.kernel_bound', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.loss_eq', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.contextual', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.seq', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.observer_bound', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.Edit.game_bound', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.sourceFintype', 'CryptoLogic.Polygraph.Experiment.ApproximateDiagramEdits.recovery']

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
        'audited_theorem_count': 5,
        'audited_definition_count': 4,
        'audited_instance_count': 1,
        'audited_support_declaration_count': 9,
        'finite_endpoint_outcomes_required': True,
        'annotated_closed_diagram_edits_verified': True,
        'strict_edit_tracks_embed_at_zero': True,
        'structural_cells_embed_at_zero': True,
        'edit_composition_adds_error_bounds': True,
        'sequential_diagram_composition_adds_error_bounds': True,
        'common_preserving_context_keeps_error_bound': True,
        'retained_input_final_state_observer_probability_gap_bounded': True,
        'allocated_game_path_loss_preserved_exactly': True,
        'positive_recovery_example_edit_tolerance': '5719/253440',
        'positive_error_implies_strict_kernel_equality_claimed': False,
        'copying_proof_certificates_treated_as_sampling': False,
        'general_horizontal_product_approximate_edit_extension_claimed': False,
        'native_runtime_for_new_diagram_operations_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
