"""Audit full-grid exact-recovery obstruction on a concrete five-state edge.

Equal finite cardinality forces recoverable stochastic kernels to be
permutations. The actual cipher edge has unequal atom-mass multisets. The
obstruction covers arbitrary ambient state kernels and arbitrary game paths,
without assuming a selected coupling or a time bound. It does not rule out
noninvertible coherence, approximate recovery, or refined retained states.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.RecoveryRigidity'
DECLARATIONS = ['Foundation.Probability.KernelRecovery.equal_card_separated_pure', 'Foundation.Probability.KernelRecovery.equal_card_recovery_pure', 'Foundation.Probability.KernelRecovery.equal_card_preserving_recovery', 'Foundation.Probability.KernelRecovery.equal_card_preserving_atom', 'Foundation.Probability.RecoveryViewTransport.forward', 'Foundation.Probability.RecoveryViewTransport.reverse', 'Foundation.Probability.RecoveryViewTransport.used_target_in_view', 'Foundation.Probability.RecoveryViewTransport.induced_preserves', 'Foundation.Probability.RecoveryViewTransport.induced_recovers', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.chain', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.chain_valid', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.edge', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source_counts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target_counts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.keyLaw', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.key_atom', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.source_full', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.target_full', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.unmatched_atom', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.no_exact_recoverable_transport', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.not_every_edge_exactly_recoverable', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryRigidity.joint_law_factor', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.stateView', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.readState', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.state_view_inverse', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.native_endpoint_law', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.no_full_state_exact_recovery', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.sourceGame', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.targetGame', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.no_path_recovery', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.no_identity_cell', 'CryptoLogic.Polygraph.Experiment.RecoveryRigidity.no_stationary_cell']
THEOREM_COUNT = 24
DEFINITION_COUNT = 10

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
        'equal_cardinality_separated_kernels_are_pure_permutations': True,
        'equal_cardinality_preserving_recovery_preserves_atom_masses_up_to_permutation': True,
        'ambient_state_recovery_transports_to_faithful_finite_views': True,
        'grid_source_vertex': [1, 2, 3],
        'grid_target_vertex': [1, 2, 4],
        'actual_grid_edge_verified': True,
        'source_absolute_atom_counts': [43, 43, 42, 111, 17],
        'target_absolute_atom_counts': [45, 44, 39, 111, 17],
        'denominator': 256,
        'both_five_state_supports_full': True,
        'no_preserving_exactly_recoverable_transport_for_any_coupling': True,
        'no_arbitrary_full_cell_state_kernel_pair_with_exact_recovery': True,
        'native_930_step_endpoint_full_cell_laws_connected': True,
        'arbitrary_source_and_target_terminal_control_views_supported': True,
        'no_roundtrip_identity_four_cell_for_any_intervening_game_paths': True,
        'no_identity_kernel_stationary_cell_regardless_of_loss_budget': True,
        'all_grid_edges_exactly_recoverable_family_ruled_out': True,
        'general_noninvertible_coherence_ruled_out': False,
        'approximate_recovery_ruled_out': False,
        'additional_retained_state_ruled_out': False,
        'previous_two_to_five_state_native_recovery_invalidated': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
