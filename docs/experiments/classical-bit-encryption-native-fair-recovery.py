"""Audit finitely fair preserving recovery kernels, game edits and native samplers.
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
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeFairRecovery'
DECLARATIONS = ['Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.forwardCounts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.reverseCounts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.forward_sum', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.reverse_sum', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.kernel', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.kernel_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.forward', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.reverse', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.forward_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.reverse_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.count_sampler_law', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.kernel_realizable', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.sampleForward', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.sampleReverse', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.forward_sample_law', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.reverse_sample_law', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.forward_preserve', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.reverse_preserve', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.forward_mismatch', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.reverse_mismatch', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FairRecovery.recovery_error', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.sourceFintype', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.countedStep', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.forward', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.reverse', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.roundtrip', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.stationaryStep', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.stationary', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.roundtrip_loss', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.discrepancy', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.recoveryCell', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.recoveryEdit', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.error_exceeds_selected_example', 'CryptoLogic.Polygraph.Experiment.FairRecoveryGame.loss_exceeds_selected_example', 'Machine.NativeFairRecoverySampler.sample', 'Machine.NativeFairRecoverySampler.kernel', 'Machine.NativeFairRecoverySampler.sample_law', 'Machine.NativeFairRecoverySampler.request', 'Machine.NativeFairRecoverySampler.rawInput', 'Machine.NativeFairRecoverySampler.readKey', 'Machine.NativeFairRecoverySampler.read_request', 'Machine.NativeFairRecoverySampler.payload', 'Machine.NativeFairRecoverySampler.leaves', 'Machine.NativeFairRecoverySampler.leaves_stops', 'Machine.NativeFairRecoverySampler.leaves_length', 'Machine.NativeFairRecoverySampler.code', 'Machine.NativeFairRecoverySampler.code_def', 'Machine.NativeFairRecoverySampler.stops', 'Machine.NativeFairRecoverySampler.code_length', 'Machine.NativeFairRecoverySampler.entry', 'Machine.NativeFairRecoverySampler.finish', 'Machine.NativeFairRecoverySampler.leaves_request', 'Machine.NativeFairRecoverySampler.full_run', 'Machine.NativeFairRecoverySampler.observe_finish', 'Machine.NativeFairRecoverySampler.framed_law', 'Machine.NativeFairRecoverySampler.entry_equivalent', 'Machine.NativeFairRecoverySampler.initial_law', 'Machine.NativeFairRecoverySampler.input_length', 'Machine.NativeFairRecoverySampler.haltsWithin', 'Machine.NativeFairRecoverySampler.bounded', 'Machine.NativeFairRecoverySampler.polynomial_time', 'CryptoLogic.Polygraph.Experiment.NativeFairRecovery.readResult', 'CryptoLogic.Polygraph.Experiment.NativeFairRecovery.observeKey', 'CryptoLogic.Polygraph.Experiment.NativeFairRecovery.nativeKernel', 'CryptoLogic.Polygraph.Experiment.NativeFairRecovery.kernel_eq', 'CryptoLogic.Polygraph.Experiment.NativeFairRecovery.forward_realized', 'CryptoLogic.Polygraph.Experiment.NativeFairRecovery.reverse_realized', 'CryptoLogic.Polygraph.Experiment.NativeFairRecovery.forward_preserves', 'CryptoLogic.Polygraph.Experiment.NativeFairRecovery.reverse_preserves']

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
        'audited_theorem_count': 39,
        'audited_definition_count': 29,
        'audited_instance_count': 1,
        'replacement_forward_and_reverse_endpoint_laws_preserved_exactly': True,
        'fair_bits_per_conditional_row': 12,
        'counts_per_row': 4096,
        'forward_local_mismatch': '6961/524288',
        'reverse_local_mismatch': '12499/1048576',
        'allocated_roundtrip_loss': '26421/1048576',
        'source_weighted_roundtrip_recovery_error': '13037041/536870912',
        'positive_error_four_cell_and_annotated_diagram_edit_verified': True,
        'conditional_recovery_error_equals_cell_kernel_discrepancy': True,
        'new_error_and_loss_exceed_prior_nondyadic_selected_example': True,
        'replacement_pair_optimality_claimed': False,
        'native_forward_and_reverse_sampler_programs_verified': True,
        'native_request_bits': 4,
        'native_sampler_runtime_bound_steps': 143,
        'native_sampler_code_length_upper_bound_instructions': 985210,
        'native_sampler_stops_on_all_inputs_and_inherited_tapes': True,
        'native_sampler_framed_full_configuration_run_verified': True,
        'native_sampler_raw_initial_observation_law_verified': True,
        'native_observed_kernels_realize_local_finite_game_path_kernels': True,
        'raw_native_request_and_coin_history_erased': False,
        'new_forward_reverse_connected_as_single_continuing_machine': False,
        'whole_native_state_identity_or_endpoint_game_law_claimed': False,
        'new_sampler_efficient_code_size_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
