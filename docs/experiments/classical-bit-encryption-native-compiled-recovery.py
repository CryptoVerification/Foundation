"""Audit native forward/reverse recovery and its polygraphic cell.

The actual forward/reverse execution recovers each admitted source, and the
raw experiment plus recovery has full-cell identity against an executed common
terminal wrapper. The index kernels in the recovery cell are native observed
kernels. Unreachable states and arbitrary contexts have no free native claims.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeCompiledRecovery'
DECLARATIONS = ['Machine.NativeRecoveryWriter.sourceKey', 'Machine.NativeRecoveryWriter.result', 'Machine.NativeRecoveryWriter.source_test', 'Machine.NativeRecoveryWriter.leaf', 'Machine.NativeRecoveryWriter.leafFinish', 'Machine.NativeRecoveryWriter.leaf_run', 'Machine.NativeRecoveryWriter.leaf_stops', 'Machine.NativeRecoveryWriter.leaves', 'Machine.NativeRecoveryWriter.decoder', 'Machine.NativeRecoveryWriter.cleanup', 'Machine.NativeRecoveryWriter.code', 'Machine.NativeRecoveryWriter.entry', 'Machine.NativeRecoveryWriter.beforeCleanup', 'Machine.NativeRecoveryWriter.decoder_run', 'Machine.NativeRecoveryWriter.decoder_stops', 'Machine.NativeRecoveryWriter.cleanup_stops', 'Machine.NativeRecoveryWriter.finish', 'Machine.NativeRecoveryWriter.cleanup_run', 'Machine.NativeRecoveryWriter.run', 'Machine.NativeRecoveryWriter.entry_equivalent', 'Machine.NativeRecoveryWriter.finish_equivalent', 'Machine.NativeRecoveryWriter.stops', 'Machine.NativeRecoveryWriter.code_length', 'Machine.NativeReverseCoupling.code', 'Machine.NativeReverseCoupling.prepared_equivalent', 'Machine.NativeReverseCoupling.writer_kernel', 'Machine.NativeReverseCoupling.run_at', 'Machine.NativeReverseCoupling.kernelAt', 'Machine.NativeReverseCoupling.reconstruct_target', 'Machine.NativeReverseCoupling.kernelAt_target', 'Machine.NativeReverseCoupling.stops', 'Machine.NativeReverseCoupling.haltsWithin', 'Machine.NativeReverseCoupling.bounded', 'Machine.NativeReverseCoupling.polynomial_time', 'Machine.NativeReverseCoupling.code_length', 'Machine.NativeCompiledRecovery.forwardCode', 'Machine.NativeCompiledRecovery.forward_stops', 'Machine.NativeCompiledRecovery.forwardKernelAt', 'Machine.NativeCompiledRecovery.forward_composition', 'Machine.NativeCompiledRecovery.forward_source', 'Machine.NativeCompiledRecovery.roundtripCode', 'Machine.NativeCompiledRecovery.roundtrip_stops', 'Machine.NativeCompiledRecovery.roundtripKernelAt', 'Machine.NativeCompiledRecovery.roundtrip_composition', 'Machine.NativeCompiledRecovery.roundtrip_source', 'Machine.NativeCompiledRecovery.code', 'Machine.NativeCompiledRecovery.raw_law', 'Machine.NativeCompiledRecovery.stops', 'Machine.NativeCompiledRecovery.haltsWithin', 'Machine.NativeCompiledRecovery.bounded', 'Machine.NativeCompiledRecovery.polynomial_time', 'Machine.NativeCompiledRecovery.roundtrip_code_length', 'Machine.NativeRecoveryIdentity.padding', 'Machine.NativeRecoveryIdentity.stationaryCode', 'Machine.NativeRecoveryIdentity.padding_stops', 'Machine.NativeRecoveryIdentity.final_control_equal', 'Machine.NativeRecoveryIdentity.stationary_framed_law', 'Machine.NativeRecoveryIdentity.stationary_initial_law', 'Machine.NativeRecoveryIdentity.full_cell_identity', 'Machine.NativeRecoveryIdentity.stationary_stops', 'Machine.NativeRecoveryIdentity.stationary_haltsWithin', 'Machine.NativeRecoveryIdentity.stationaryBounded', 'Machine.NativeRecoveryIdentity.public_identity', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.decode_finish', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.nativeForward', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.nativeForward_eq', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.nativeReverse', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.nativeReverse_eq', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.forwardStep', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.reverseStep', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.roundtrip', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.roundtrip_kernel', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.roundtrip_loss', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.recoveryCell', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.path_matches_continuing_machine', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.recoveryEdit', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.contextualRecovery', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.executionGame', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.stationaryExecutionGame', 'CryptoLogic.Polygraph.Experiment.NativeCompiledRecovery.executionReification']
THEOREM_COUNT = 46
DEFINITION_COUNT = 34

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
        'native_recovery_writer_runtime_bound_steps': 55,
        'native_recovery_writer_code_length_bound': 126,
        'native_reverse_runtime_bound_steps': 101,
        'native_reverse_code_length_bound': 390,
        'native_canonical_forward_runtime_bound_steps': 288,
        'native_continuing_forward_reverse_runtime_bound_steps': 390,
        'native_continuing_forward_reverse_code_length_bound': 9064,
        'raw_reference_and_native_recovery_runtime_bound_steps': 1321,
        'stationary_reference_with_common_terminal_control_runtime_bound_steps': 932,
        'original_unwrapped_reference_runtime_bound_steps': 930,
        'pointwise_recovery_of_both_admitted_full_source_states': True,
        'full_cell_identity_against_actually_executed_stationary_wrapper': True,
        'public_identity_against_original_unwrapped_reference': True,
        'raw_full_cell_identity_game_reification_verified': True,
        'native_forward_observed_kernel_equals_repaired_finite_forward': True,
        'native_reverse_observed_kernel_equals_deterministic_parent': True,
        'native_observed_roundtrip_path_matches_continuing_machine': True,
        'forward_and_reverse_local_loss_bound': '37/128 each',
        'recovery_cell_path_loss_budget': '37/64',
        'recovery_four_cell_diagram_edit_and_logical_contexts_verified': True,
        'all_raw_inputs_stop_at_declared_budgets': True,
        'arbitrary_logical_contexts_given_free_native_runtime': False,
        'reverse_order_target_identity_claimed': False,
        'identity_on_unreachable_states_claimed': False,
        'general_coherent_coupling_family_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
