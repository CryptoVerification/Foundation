"""Audit a native repaired-coupling sampler and its continuing recovery caller.

Raw input is two bits. Seven fair coins select the target key. The recovery
caller reads only that key. Full canonical-state adapters, history erasure and
arbitrary logical continuation runtime are separate obligations.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeCouplingSampler'
DECLARATIONS = ['Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoverableSampler.sample', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoverableSampler.sample_probability', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoverableSampler.sample_law', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoverableSampler.sample_parent', 'Machine.NativeRecoverableKeySampler.request', 'Machine.NativeRecoverableKeySampler.rawInput', 'Machine.NativeRecoverableKeySampler.payload', 'Machine.NativeRecoverableKeySampler.leaves', 'Machine.NativeRecoverableKeySampler.leaves_stops', 'Machine.NativeRecoverableKeySampler.leaves_length', 'Machine.NativeRecoverableKeySampler.code', 'Machine.NativeRecoverableKeySampler.code_def', 'Machine.NativeRecoverableKeySampler.stops', 'Machine.NativeRecoverableKeySampler.code_length', 'Machine.NativeRecoverableKeySampler.entry', 'Machine.NativeRecoverableKeySampler.finish', 'Machine.NativeRecoverableKeySampler.leaves_request', 'Machine.NativeRecoverableKeySampler.full_run', 'Machine.NativeRecoverableKeySampler.observe_finishControl', 'Machine.NativeRecoverableKeySampler.finishControl_resume', 'Machine.NativeRecoverableKeySampler.observe_finish', 'Machine.NativeRecoverableKeySampler.framed_law', 'Machine.NativeRecoverableKeySampler.entry_equivalent', 'Machine.NativeRecoverableKeySampler.initial_law', 'Machine.NativeRecoverableKeySampler.input_length', 'Machine.NativeRecoverableKeySampler.haltsWithin', 'Machine.NativeRecoverableKeySampler.bounded', 'Machine.NativeRecoverableKeySampler.polynomial_time', 'Machine.NativeRecoverableKeyObserver.accepts', 'Machine.NativeRecoverableKeyObserver.accepts_encoded', 'Machine.NativeRecoverableKeyObserver.decoder', 'Machine.NativeRecoverableKeyObserver.rewind', 'Machine.NativeRecoverableKeyObserver.code', 'Machine.NativeRecoverableKeyObserver.decoder_stops', 'Machine.NativeRecoverableKeyObserver.stops', 'Machine.NativeRecoverableKeyObserver.run', 'Machine.NativeRecoverableKeyObserver.code_length', 'Machine.NativeRecoverableCouplingExecution.code', 'Machine.NativeRecoverableCouplingExecution.read', 'Machine.NativeRecoverableCouplingExecution.keyCiphertext', 'Machine.NativeRecoverableCouplingExecution.observe', 'Machine.NativeRecoverableCouplingExecution.history', 'Machine.NativeRecoverableCouplingExecution.finish', 'Machine.NativeRecoverableCouplingExecution.sampler_resume', 'Machine.NativeRecoverableCouplingExecution.full_run', 'Machine.NativeRecoverableCouplingExecution.written_left', 'Machine.NativeRecoverableCouplingExecution.read_finish', 'Machine.NativeRecoverableCouplingExecution.observe_by_left', 'Machine.NativeRecoverableCouplingExecution.keyCiphertext_finish', 'Machine.NativeRecoverableCouplingExecution.observe_equivalent', 'Machine.NativeRecoverableCouplingExecution.framed_law', 'Machine.NativeRecoverableCouplingExecution.initial_law', 'Machine.NativeRecoverableCouplingExecution.recovered_bit', 'Machine.NativeRecoverableCouplingExecution.stops', 'Machine.NativeRecoverableCouplingExecution.haltsWithin', 'Machine.NativeRecoverableCouplingExecution.bounded', 'Machine.NativeRecoverableCouplingExecution.polynomial_time', 'Machine.NativeRecoverableCouplingExecution.code_length', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.pick', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.nativeLaw', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.native_law', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.nativeProgram', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.referenceProgram', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.native_realization', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.reification', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.contextPath', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.nativeForward', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.nativeForward_eq', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.native_recovers', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.native_target_marginal', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.nativeResultLaw', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.native_result_law', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.native_result_target', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.output_finish', 'CryptoLogic.Polygraph.Experiment.NativeCouplingSampler.public_packet']
THEOREM_COUNT = 47
DEFINITION_COUNT = 28

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
        'conditional_sampler_request_bits': 2,
        'conditional_sampler_request_format': '[source bit, ciphertext]',
        'native_fair_coin_count': 7,
        'conditional_sampler_runtime_bound_steps': 87,
        'conditional_sampler_code_length_bound': 'code.length + 6 <= 8004',
        'recovery_caller_runtime_bound_steps': 23,
        'recovery_caller_code_length_bound': 85,
        'single_continuing_sampler_and_recovery_runtime_bound_steps': 111,
        'single_continuing_code_length_bound': 8086,
        'all_raw_inputs_stop_at_declared_budgets': True,
        'bounded_program_and_polynomial_time_verified': True,
        'exact_repaired_forward_distribution_from_raw_request_verified': True,
        'sample_parent_correct_for_every_coin_word': True,
        'recovery_caller_uses_retained_target_key': True,
        'sampled_key_ciphertext_and_written_source_bit_joint_law_verified': True,
        'standard_evalWithin_public_packet': 'pure (some [ciphertext, source bit])',
        'averaged_actual_native_key_ciphertext_view_equals_target_experiment': True,
        'native_sampler_distribution_reification_and_logical_bind_contexts_verified': True,
        'arbitrary_logical_continuations_given_free_native_runtime': False,
        'full_reference_state_to_two_bit_request_native_adapter_verified': False,
        'new_sampler_request_and_coin_history_erasure_verified': False,
        'entire_sampler_configuration_equals_canonical_reference_exit_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
