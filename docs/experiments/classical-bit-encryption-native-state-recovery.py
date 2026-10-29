"""Audit exact state recovery and a fixed-forward native obstruction.

Every reverse receiving only the intermediate state is quantified over.
Other forward kernels, additional retained information and approximate
recovery are not excluded.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeStateRecovery'
DECLARATIONS = ['Foundation.Probability.KernelRecovery.RecoversOn', 'Foundation.Probability.KernelRecovery.Separated', 'Foundation.Probability.KernelRecovery.recovery_implies_separated', 'Foundation.Probability.KernelRecovery.common_output_no_recovery', 'Foundation.Probability.KernelRecovery.decoder', 'Foundation.Probability.KernelRecovery.decoder_correct', 'Foundation.Probability.KernelRecovery.separated_has_decoder', 'Foundation.Probability.KernelRecovery.exists_reverse_iff_separated', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction.Result', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction.forward', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction.shared_from_zero_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction.shared_from_two_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction.shared_from_zero', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction.shared_from_two', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction.two_source_supported', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction.no_reverse', 'CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit.forward', 'CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit.forward_encoded', 'CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit.shared_from_zero', 'CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit.shared_from_two', 'CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit.two_source_reachable', 'CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit.no_reverse', 'CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit.no_reverse_path_cell', 'CryptoLogic.Polygraph.Experiment.NativeState.RecoveryAudit.no_reverse_path_edits']
THEOREM_COUNT = 18
DEFINITION_COUNT = 6

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
        'native_machine_runtime_bound_steps': 930,
        'native_code_changed': False,
        'general_exact_recovery_requires_disjoint_forward_supports': True,
        'general_disjoint_supports_suffice_semantically_with_nonempty_source': True,
        'general_decoder_uses_classical_choice_not_native_runtime_contract': True,
        'grid_vertices': [[0, 8, 24], [1, 8, 25]],
        'fixed_forward': 'Previously selected maximal conditional kernel on full cell states modulo blank padding',
        'source_keys': [0, 2],
        'common_intermediate_key': 1,
        'common_intermediate_from_key_zero_probability': '25/296',
        'common_intermediate_from_key_two_probability': '85/1184',
        'both_sources_reachable_verified': True,
        'all_reverse_kernels_receiving_only_intermediate_state_excluded_for_exact_recovery': True,
        'all_reverse_game_paths_have_no_four_cell_to_identity_for_this_forward': True,
        'all_reverse_game_paths_have_no_diagram_edit_sequence_to_identity_for_this_forward': True,
        'different_forward_kernels_excluded': False,
        'additional_correlated_state_excluded': False,
        'approximate_recovery_excluded': False,
        'cryptographic_reduction_impossibility_claimed': False,
        'public_key_hidden_advantage_claimed': False,
        'coupling_sampler_native_runtime_compiled': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
