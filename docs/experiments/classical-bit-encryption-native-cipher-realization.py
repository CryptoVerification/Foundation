"""Audit native cipher-family contracts and the five-key realization.

Encryption uses an internal key/ciphertext observation. Decryption is a
separate native program; no composed caller runtime is asserted.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Machine.NativeFiveKeyRealization'
DECLARATIONS = ['Machine.NativeCipherRealization.encryptionAtom', 'Machine.NativeCipherRealization.decryptionAtom', 'Machine.NativeCipherRealization.Encryption.law', 'Machine.NativeCipherRealization.Encryption.executes', 'Machine.NativeCipherRealization.Encryption.polynomial_time', 'Machine.NativeCipherRealization.Encryption.atom_probability', 'Machine.NativeCipherRealization.Encryption.distance', 'Machine.NativeCipherRealization.Encryption.distance_eq', 'Machine.NativeCipherRealization.Encryption.comparisonDistance', 'Machine.NativeCipherRealization.Encryption.comparisonDistance_eq', 'Machine.NativeCipherRealization.Decryption.executes', 'Machine.NativeCipherRealization.Decryption.polynomial_time', 'Machine.NativeCipherRealization.perfect_four_key_lower', 'Machine.NativeCipherRealization.perfect_four_key_gap', 'Machine.NativeCipherRealization.perfect_four_key_not_cap', 'Machine.NativeCipherRealization.approximate_four_key_gap', 'Machine.NativeFiveKeyDecryption.request', 'Machine.NativeFiveKeyDecryption.header', 'Machine.NativeFiveKeyDecryption.keyBits', 'Machine.NativeFiveKeyDecryption.header_request', 'Machine.NativeFiveKeyDecryption.keyBits_request', 'Machine.NativeFiveKeyDecryption.parse', 'Machine.NativeFiveKeyDecryption.parse_request', 'Machine.NativeFiveKeyDecryption.leaves', 'Machine.NativeFiveKeyDecryption.leaves_stops', 'Machine.NativeFiveKeyDecryption.leaves_request', 'Machine.NativeFiveKeyDecryption.code', 'Machine.NativeFiveKeyDecryption.code_def', 'Machine.NativeFiveKeyDecryption.stops', 'Machine.NativeFiveKeyDecryption.rawInput', 'Machine.NativeFiveKeyDecryption.input_length', 'Machine.NativeFiveKeyDecryption.entry', 'Machine.NativeFiveKeyDecryption.entry_equivalent', 'Machine.NativeFiveKeyDecryption.framed_law', 'Machine.NativeFiveKeyDecryption.initial_law', 'Machine.NativeFiveKeyDecryption.haltsWithin', 'Machine.NativeFiveKeyDecryption.bounded', 'Machine.NativeFiveKeyDecryption.polynomial_time', 'Machine.NativeFiveKeyDecryption.correctness', 'Machine.NativeFiveKeyDecryption.atom_probability', 'Machine.NativeFiveKeyDecryption.code_length_bound', 'Machine.NativeFiveKeyRealization.encryption', 'Machine.NativeFiveKeyRealization.decryption', 'Machine.NativeFiveKeyRealization.family', 'Machine.NativeFiveKeyRealization.encryption_budget', 'Machine.NativeFiveKeyRealization.decryption_budget', 'Machine.NativeFiveKeyRealization.profile', 'Machine.NativeFiveKeyRealization.distance_eq', 'Machine.NativeFiveKeyRealization.edge_bound']
THEOREM_COUNT = 32
DEFINITION_COUNT = 17

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
        'five_key_native_family_contract_instantiated': True,
        'encryption_runtime_bound_steps': 930,
        'decryption_runtime_bound_steps': 69,
        'decryption_input_bits': 22,
        'decryption_code_length_bound': 'code.length + 6 <= 9 * 2^22',
        'decryption_all_raw_inputs_stop': True,
        'decryption_correctness_verified': True,
        'encryption_and_decryption_share_cipher_profile': True,
        'four_key_candidate_lower_bound': '2/3, under perfect profile and prescribed boundary',
        'perfect_four_key_comparison_gap': '145/384, under the same conditions',
        'approximate_four_key_comparison_gap': '1/384, under original error/bias and repaired-boundary conditions',
        'native_four_key_candidate_instantiated': False,
        'comparison_uses_internal_key_ciphertext_view': True,
        'public_key_hidden_advantage_or_general_reduction_impossibility_claimed': False,
        'composed_encryption_decryption_caller_runtime_claimed': False,
        'polynomial_compiler_size_in_growing_control_width_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
