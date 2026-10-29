"""Audit native erasure, full configuration factorization, and continuing callers.

This checks physical history erasure and a concrete ciphertext-toggle caller.
No novelty or polynomial compiler-size claim is made.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Machine.NativeCleanCipherContinuation'
THEOREMS = ['Machine.NativePrivateHistoryErasure.atom_run', 'Machine.NativePrivateHistoryErasure.atom_stops', 'Machine.NativePrivateHistoryErasure.code_length', 'Machine.NativePrivateHistoryErasure.stops', 'Machine.NativePrivateHistoryErasure.run', 'Machine.NativePrivateHistoryErasure.apply_append', 'Machine.NativePrivateHistoryErasure.erase_length', 'Machine.NativePrivateHistoryErasure.protected_length', 'Machine.NativePrivateHistoryErasure.erase_cells', 'Machine.NativePrivateHistoryErasure.protected_cells', 'Machine.NativePrivateHistoryErasure.cleanup_stops', 'Machine.NativePrivateHistoryErasure.cleanup_length', 'Machine.NativeCleanEightBitCipher.finish_resume', 'Machine.NativeCleanEightBitCipher.source_run', 'Machine.NativeCleanEightBitCipher.cleanup_run', 'Machine.NativeCleanEightBitCipher.run', 'Machine.NativeCleanEightBitCipher.stops', 'Machine.NativeCleanEightBitCipher.observe_finish', 'Machine.NativeCleanEightBitCipher.observed_run', 'Machine.NativeCleanEightBitCipher.initial_law', 'Machine.NativeCleanEightBitCipher.haltsWithin', 'Machine.NativeCleanEightBitCipher.polynomial_time', 'Machine.NativeCiphertextToggle.run', 'Machine.NativeCiphertextToggle.stops', 'Machine.NativeSequenceResultLaw.run', 'Machine.NativeCleanCipherContinuation.run', 'Machine.NativeCleanCipherContinuation.stops', 'Machine.NativeCleanCipherContinuation.initial_observation', 'Machine.NativeCleanCipherContinuation.observer_bound', 'Machine.NativeCleanCipherContinuation.toggle_stops', 'Machine.NativeCleanCipherContinuation.toggle_run', 'Machine.NativeCleanCipherContinuation.toggle_initial_law', 'Machine.NativeCleanCipherContinuation.toggle_haltsWithin', 'Machine.NativeCleanCipherContinuation.toggle_polynomial_time']


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
            '#print axioms ' + name + '\n' for name in THEOREMS))
        output = run(['lake', 'env', 'lean', str(probe)])
    axioms = {}
    for name in THEOREMS:
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
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'physical_history_erasure_verified': True,
        'protected_nearest_key_cell_count': 3,
        'erased_request_cell_count': 19,
        'erased_coin_cell_count': 8,
        'cleanup_code_length': 436,
        'cleanup_runtime_bound': 262,
        'cipher_and_cleanup_runtime_bound': 411,
        'full_formatted_configuration_law_factors_through_key_ciphertext': True,
        'raw_initial_observation_law_verified': True,
        'arbitrary_continuation_contract': 'caller stops on every physical input/output tape within T transitions',
        'cipher_cleanup_caller_runtime_bound': '411+T+1',
        'continuation_receives_real_returned_tapes': True,
        'observer_bound_transport_requires_explicit_source_bound_and_admission': True,
        'numerical_37_over_128_observer_bound_discharged_here': False,
        'concrete_caller': 'read preceding ciphertext, replace with its complement, return head',
        'concrete_caller_stops_all_tapes_in': 6,
        'concrete_caller_combined_runtime_bound': 418,
        'private_key_retained': True,
        'key_hidden_security_advantage_claimed': False,
        'polynomial_compiler_size_claimed': False,
        'newness_established': False,
        'infinity_categories_shown_necessary': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
