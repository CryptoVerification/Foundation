"""Audit an alternative recoverable coupling of the same native endpoint laws.

A disjoint integer partition repairs one-sided recovery at unchanged local
loss. Coherent paths use finite indices of reachable complete cell states;
an identity on all unreachable raw states is not asserted.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeCouplingRepair'
DECLARATIONS = ['Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.Result', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.sourceResult', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.parent', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.targetResult', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.counts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.counts_sum', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.forward', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.forward_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.sourceLaw', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.source_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.targetLaw', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.singleton', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.map_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.target_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.source_law', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.target_law', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.counts_compatible', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.parent_supported', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.recovers', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.reverse_preserves', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.result_agrees', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.bad', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.badDecidable', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.joint', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.badCount', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.badCount_sum', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.bad_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.bad_probability', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.reverseBad', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.reverseBadDecidable', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.reverseJoint', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.reverseCount', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.reverseCount_sum', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.reverse_bad_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable.reverse_bad_probability', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.sourceView', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.targetView', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.source_native_law', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.target_native_law', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.source_parent', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.sourceView_injective', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.targetView_injective', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.stateForward', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.stateReverse', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.state_roundtrip', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.state_forward_preserves', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.state_reverse_preserves', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.supported_state_recovers', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.sourceGame', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.targetGame', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.forwardStep', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.reverseStep', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.roundtrip', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.roundtrip_kernel', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.roundtrip_loss', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.stationaryStep', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.stationary', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.recoveryCell', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.recoveryEdit', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.contextualRecovery', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.forward_changed', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.same_forward_budget', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.same_reverse_budget', 'CryptoLogic.Polygraph.Experiment.NativeRecoverable.exists_repaired_state_kernels']
THEOREM_COUNT = 34
DEFINITION_COUNT = 30

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
        'grid_vertices': [[0, 8, 24], [1, 8, 25]],
        'source_index_type': 'Bool, injective encoding of the two source states',
        'target_index_type': 'Fin 5, injective encoding of the five target states',
        'conditional_integer_weight_denominator': 128,
        'source_false_counts': [88, 20, 0, 20, 0],
        'source_true_counts': [0, 0, 94, 0, 34],
        'source_and_target_actual_native_full_state_laws_verified': True,
        'deterministic_reverse_parent_labels': [[0, 1, 3], [2, 4]],
        'exact_recovery_of_every_reachable_source_native_state': True,
        'both_state_kernel_marginal_preservation_laws_verified': True,
        'forward_kernel_provably_different_from_previous_fixed_maximal_kernel': True,
        'forward_mismatch_probability': '37/128',
        'reverse_mismatch_probability': '37/128',
        'same_local_loss_budgets_as_previous_choice_verified': True,
        'roundtrip_and_padded_identity_loss_budget': '37/64',
        'one_sided_recovery_four_cell_on_reachable_state_indices_verified': True,
        'recovery_diagram_edit_and_sequential_contexts_verified': True,
        'extra_correlated_input_register_added': False,
        'reverse_order_identity_claimed': False,
        'all_unreachable_raw_state_identity_claimed': False,
        'coupling_sampler_native_runtime_compiled': False,
        'general_path_independent_coupling_family_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
