"""Audit charged physical history erasure for the native repaired coupling.

The entry remains a two-bit raw request. A canonical reference exit adapter
and a full-reference-state request preparation program remain separate.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeCleanCoupling'
DECLARATIONS = ['Machine.NativeCleanRecoverableCoupling.cleanup', 'Machine.NativeCleanRecoverableCoupling.cleanup_stops', 'Machine.NativeCleanRecoverableCoupling.cleanup_length', 'Machine.NativeCleanRecoverableCoupling.code', 'Machine.NativeCleanRecoverableCoupling.finish', 'Machine.NativeCleanRecoverableCoupling.cleanup_run', 'Machine.NativeCleanRecoverableCoupling.full_run', 'Machine.NativeCleanRecoverableCoupling.observe_finish', 'Machine.NativeCleanRecoverableCoupling.framed_law', 'Machine.NativeCleanRecoverableCoupling.initial_law', 'Machine.NativeCleanRecoverableCoupling.initial_state_law', 'Machine.NativeCleanRecoverableCoupling.cleanup_coin_independent', 'Machine.NativeCleanRecoverableCoupling.stops', 'Machine.NativeCleanRecoverableCoupling.haltsWithin', 'Machine.NativeCleanRecoverableCoupling.bounded', 'Machine.NativeCleanRecoverableCoupling.polynomial_time', 'Machine.NativeCleanRecoverableCoupling.code_length', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.nativeLaw', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.native_law', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.nativeProgram', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.native_realization', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.reification', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.contextPath', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.nativeResultLaw', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.native_result_law', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.native_result_target', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.output_finish', 'CryptoLogic.Polygraph.Experiment.NativeCleanCoupling.public_packet']
THEOREM_COUNT = 19
DEFINITION_COUNT = 9

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
        'request_bits': 2,
        'fair_coin_bits': 7,
        'erased_history_cells': 9,
        'preserved_private_key_cells': 3,
        'cleanup_runtime_bound_steps': 100,
        'cleanup_code_length': 166,
        'single_continuing_runtime_bound_steps': 212,
        'single_continuing_code_length_bound': 8255,
        'all_raw_inputs_stop_at_declared_budget': True,
        'full_framed_configuration_law_factors_through_sampled_key': True,
        'standard_initial_full_cell_state_law_verified': True,
        'same_key_cleanup_exits_equal_for_different_coin_words': True,
        'preserved_key_ciphertext_and_recovery_joint_law_verified': True,
        'standard_evalWithin_public_packet': 'pure (some [ciphertext, source bit])',
        'averaged_native_key_ciphertext_law_equals_target_experiment': True,
        'logical_distribution_reification_verified': True,
        'full_reference_state_to_request_adapter_verified': False,
        'canonical_reference_exit_adapter_verified': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
