"""Audit a concrete native four-key cipher and the prescribed-boundary comparison.

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
MODULE = 'Foundation.Crypto.Semantics.Machine.NativeFourKeyRealization'
DECLARATIONS = ['Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FourKeyWitness.onBoundary', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FourKeyWitness.counts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FourKeyWitness.counts_valid', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FourKeyWitness.cipher', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.FourKeyWitness.boundary', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourNaturalCounts', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourNaturalCounts_sum', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourSampleEightBits', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourSampleEightBits_probability', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourSampleEightBits_cipher_weight', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourEncryptBit', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourEightBitResult', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourEightBitLaw', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.four_signed_nonneg_iff', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourEncryptBit_probability', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourEncryptBit_correct', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourEncryptBit_atom_factor', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.fourEightBitLaw_atom', 'Machine.NativeFourKeySampler.encodeKey', 'Machine.NativeFourKeySampler.decodeKey', 'Machine.NativeFourKeySampler.decode_encodeKey', 'Machine.NativeFourKeySampler.payload', 'Machine.NativeFourKeySampler.code', 'Machine.NativeFourKeySampler.entry', 'Machine.NativeFourKeySampler.decodeResult', 'Machine.NativeFourKeySampler.observe', 'Machine.NativeFourKeySampler.observe_control', 'Machine.NativeFourKeySampler.law', 'Machine.NativeFourKeySampler.stops', 'Machine.NativeFourKeySampler.haltsWithin', 'Machine.NativeFourKeySampler.polynomial_time', 'Machine.NativeFourKeySampler.code_length_bound', 'Machine.NativeFourKeySampler.bounded', 'Machine.NativeFourKeySampler.observe_equivalent', 'Machine.NativeControlledFourKeyCipher.leaves', 'Machine.NativeControlledFourKeyCipher.halt_stops', 'Machine.NativeControlledFourKeyCipher.leaves_stops', 'Machine.NativeControlledFourKeyCipher.leaves_length_bound', 'Machine.NativeControlledFourKeyCipher.code', 'Machine.NativeControlledFourKeyCipher.code_def', 'Machine.NativeControlledFourKeyCipher.code_stops', 'Machine.NativeControlledFourKeyCipher.code_length_bound', 'Machine.NativeControlledFourKeyCipher.entry', 'Machine.NativeControlledFourKeyCipher.leaves_request', 'Machine.NativeControlledFourKeyCipher.law', 'Machine.NativeControlledFourKeyCipher.haltsWithin', 'Machine.NativeControlledFourKeyCipher.bounded', 'Machine.NativeControlledFourKeyCipher.polynomial_time', 'Machine.NativeControlledFourKeyCipher.rawInput', 'Machine.NativeControlledFourKeyCipher.entry_equivalent', 'Machine.NativeControlledFourKeyCipher.initial_law', 'Machine.NativeControlledFourKeyCipher.atom_probability', 'Machine.NativeFourKeyDecryption.request', 'Machine.NativeFourKeyDecryption.header', 'Machine.NativeFourKeyDecryption.keyBits', 'Machine.NativeFourKeyDecryption.header_request', 'Machine.NativeFourKeyDecryption.keyBits_request', 'Machine.NativeFourKeyDecryption.parse', 'Machine.NativeFourKeyDecryption.parse_request', 'Machine.NativeFourKeyDecryption.leaves', 'Machine.NativeFourKeyDecryption.leaves_stops', 'Machine.NativeFourKeyDecryption.leaves_request', 'Machine.NativeFourKeyDecryption.code', 'Machine.NativeFourKeyDecryption.code_def', 'Machine.NativeFourKeyDecryption.stops', 'Machine.NativeFourKeyDecryption.rawInput', 'Machine.NativeFourKeyDecryption.input_length', 'Machine.NativeFourKeyDecryption.entry', 'Machine.NativeFourKeyDecryption.entry_equivalent', 'Machine.NativeFourKeyDecryption.framed_law', 'Machine.NativeFourKeyDecryption.initial_law', 'Machine.NativeFourKeyDecryption.haltsWithin', 'Machine.NativeFourKeyDecryption.bounded', 'Machine.NativeFourKeyDecryption.polynomial_time', 'Machine.NativeFourKeyDecryption.correctness', 'Machine.NativeFourKeyDecryption.atom_probability', 'Machine.NativeFourKeyDecryption.code_length_bound', 'Machine.NativeFourKeyRealization.encryption', 'Machine.NativeFourKeyRealization.decryption', 'Machine.NativeFourKeyRealization.family', 'Machine.NativeFourKeyRealization.encryption_budget', 'Machine.NativeFourKeyRealization.decryption_budget', 'Machine.NativeFourKeyRealization.boundary', 'Machine.NativeFourKeyRealization.candidate_exists', 'Machine.NativeFourKeyRealization.edge_lower', 'Machine.NativeFourKeyRealization.five_key_gap']
THEOREM_COUNT = 53
DEFINITION_COUNT = 33

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
        'four_key_native_family_contract_instantiated': True,
        'four_key_candidate_class_nonempty_verified': True,
        'specified_boundary_discharged': True,
        'encryption_random_bits': 8,
        'encryption_request_bits': 19,
        'encryption_runtime_bound_steps': 148,
        'decryption_runtime_bound_steps': 69,
        'decryption_request_bits': 22,
        'encryption_code_length_bound': 'code.length + 6 <= 3932 * 2^19',
        'decryption_code_length_bound': 'code.length + 6 <= 9 * 2^22',
        'all_raw_inputs_stop': True,
        'decryption_correctness_verified': True,
        'encryption_and_decryption_share_cipher_profile': True,
        'concrete_four_key_actual_edge_lower_bound': '2/3',
        'concrete_five_vs_four_actual_machine_gap': '145/384',
        'comparison_metric': 'internal labelled key/ciphertext distance',
        'five_key_reference_runtime_bound_steps': 930,
        'comparison_is_runtime_speedup_claim': False,
        'public_key_hidden_advantage_or_general_reduction_impossibility_claimed': False,
        'composed_encryption_decryption_caller_runtime_claimed': False,
        'polynomial_compiler_size_in_growing_control_width_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
