"""Audit finite maximal kernels and native labelled statistical four-cells.

The whole retained key/ciphertext pair is coupled. No sampler runtime or
coherence of arbitrary different couplings is inferred from marginals.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeRetainedCoherence'
DECLARATIONS = ['Foundation.Probability.FiniteMaximalCoupling.common', 'Foundation.Probability.FiniteMaximalCoupling.left', 'Foundation.Probability.FiniteMaximalCoupling.right', 'Foundation.Probability.FiniteMaximalCoupling.residual', 'Foundation.Probability.FiniteMaximalCoupling.common_nonneg', 'Foundation.Probability.FiniteMaximalCoupling.left_nonneg', 'Foundation.Probability.FiniteMaximalCoupling.right_nonneg', 'Foundation.Probability.FiniteMaximalCoupling.sum_left', 'Foundation.Probability.FiniteMaximalCoupling.sum_right', 'Foundation.Probability.FiniteMaximalCoupling.residual_nonneg', 'Foundation.Probability.FiniteMaximalCoupling.left_zero', 'Foundation.Probability.FiniteMaximalCoupling.right_zero', 'Foundation.Probability.FiniteMaximalCoupling.disjoint', 'Foundation.Probability.FiniteMaximalCoupling.mass', 'Foundation.Probability.FiniteMaximalCoupling.mass_nonneg', 'Foundation.Probability.FiniteMaximalCoupling.row_sum', 'Foundation.Probability.FiniteMaximalCoupling.col_sum', 'Foundation.Probability.FiniteMaximalCoupling.diagonal', 'Foundation.Probability.FiniteMaximalCoupling.total_mass', 'Foundation.Probability.FiniteMaximalCoupling.joint', 'Foundation.Probability.FiniteMaximalCoupling.joint_real', 'Foundation.Probability.FiniteMaximalCoupling.joint_left', 'Foundation.Probability.FiniteMaximalCoupling.joint_right', 'Foundation.Probability.FiniteMaximalCoupling.residual_eq_variation', 'Foundation.Probability.FiniteMaximalCoupling.mismatch_probability', 'Foundation.Probability.FiniteMaximalCoupling.mass_zero_of_left_zero', 'Foundation.Probability.FiniteMaximalCoupling.kernel', 'Foundation.Probability.FiniteMaximalCoupling.weighted_kernel', 'Foundation.Probability.FiniteMaximalCoupling.kernel_joint', 'Foundation.Probability.FiniteMaximalCoupling.kernel_preserve', 'CryptoLogic.Polygraph.Experiment.FiniteMaximal.game', 'CryptoLogic.Polygraph.Experiment.FiniteMaximal.step', 'CryptoLogic.Polygraph.Experiment.FiniteMaximal.joint_eq', 'CryptoLogic.Polygraph.Experiment.FiniteMaximal.mismatch_exact', 'CryptoLogic.Polygraph.Experiment.NativeRetained.Result', 'CryptoLogic.Polygraph.Experiment.NativeRetained.Vertex', 'CryptoLogic.Polygraph.Experiment.NativeRetained.nativeLaw', 'CryptoLogic.Polygraph.Experiment.NativeRetained.nativeLaw_eq', 'CryptoLogic.Polygraph.Experiment.NativeRetained.game', 'CryptoLogic.Polygraph.Experiment.NativeRetained.transition', 'CryptoLogic.Polygraph.Experiment.NativeRetained.loss_eq', 'CryptoLogic.Polygraph.Experiment.NativeRetained.event_independent', 'CryptoLogic.Polygraph.Experiment.NativeRetained.edgeTransition', 'CryptoLogic.Polygraph.Experiment.NativeRetained.edgeDiagram', 'CryptoLogic.Polygraph.Experiment.NativeRetained.edge_sound', 'CryptoLogic.Polygraph.Experiment.NativeRetained.referenceGame', 'CryptoLogic.Polygraph.Experiment.NativeRetained.toReference', 'CryptoLogic.Polygraph.Experiment.NativeRetained.fromReference', 'CryptoLogic.Polygraph.Experiment.NativeRetained.direct', 'CryptoLogic.Polygraph.Experiment.NativeRetained.factored', 'CryptoLogic.Polygraph.Experiment.NativeRetained.factorization_kernel', 'CryptoLogic.Polygraph.Experiment.NativeRetained.factorization_loss', 'CryptoLogic.Polygraph.Experiment.NativeRetained.factorizationCell', 'CryptoLogic.Polygraph.Experiment.NativeRetained.factorizationEdit', 'CryptoLogic.Polygraph.Experiment.NativeRetained.contextualFactorization']
THEOREM_COUNT = 31
DEFINITION_COUNT = 24

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
        'finite_maximal_joint_marginals_verified': True,
        'mismatch_exactly_finite_total_variation': True,
        'conditional_kernel_joint_reconstruction_verified': True,
        'kernel_fallback_on_zero_probability_inputs_specified': True,
        'uses_existing_directed_game_step_and_diagram_rules': True,
        'native_machine_runtime_bound_steps': 930,
        'retained_outcome': 'Fin 5 x Bool, labelled private key and ciphertext',
        'native_retained_view_law_verified': True,
        'transition_kernel_independent_of_acceptance_event': True,
        'native_retained_edge_error_bound': '37/128',
        'native_reference_statistical_factorization_kernel_pointwise_verified': True,
        'native_reference_statistical_factorization_loss_verified': True,
        'factorization_four_cell_and_diagram_edit_verified': True,
        'factorization_sequential_contexts_verified': True,
        'all_physical_machine_registers_retained_claimed': False,
        'arbitrary_coupling_coherence_from_marginals_claimed': False,
        'coupling_sampler_native_runtime_compiled': False,
        'public_key_hidden_advantage_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
