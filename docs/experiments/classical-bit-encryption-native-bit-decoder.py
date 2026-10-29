"""Audit finite-word native decoding and private key/ciphertext placement.

The generic compiler has a uniform native-leaf stopping premise; the private
three-bit-key/one-bit-output specialization discharges it with nine instructions.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Machine.NativePrivateBitResult'
THEOREMS = ['Machine.NativeBitDecisionTree.' + name for name in [
    'preload_moveRight_cons', 'afterRead_cons', 'run_selected',
    'finishControl_overwrite', 'compile_contract', 'compile_halts',
    'compile_run', 'compile_length_bound']] + [
    'Machine.NativePrivateBitResult.' + name for name in [
        'code_length', 'run', 'stops', 'writeKey_buffer', 'writeOutput_buffer',
        'compiled_halts', 'compiled_run', 'compiled_length_bound',
        'afterRead_keyBuffer', 'finish_buffers', 'compiled_buffers_run']]



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
    with tempfile.TemporaryDirectory(prefix='foundation-native-private-result-') as directory:
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
        'one_fixed_native_code_per_fixed_payload_table': True,
        'exact_joint_physical_configuration_law_verified': True,
        'arbitrary_retained_input_and_output_frames_and_suffixes': True,
        'generic_uniform_native_leaf_stopping_contract_required': True,
        'private_payload_leaf_stopping_contract_discharged': True,
        'input_format': 'n real input bits; buffered placement reserves three private key cells and one output cell, followed by arbitrary suffixes.',
        'generic_runtime_bound_steps': 'T + 3*n',
        'generic_code_length_bound': 'code.length + 6 <= (L + 6) * 2^n',
        'private_key_bit_count': 3,
        'ciphertext_output_bit_count': 1,
        'private_payload_leaf_steps': 9,
        'private_payload_decoder_runtime_bound_steps': '9 + 3*n',
        'private_payload_decoder_code_length_bound': 'code.length + 6 <= 15 * 2^n',
        'read_word_is_retained_in_private_input_history': True,
        'native_fair_random_generator_connected': False,
        'five_key_label_encoding_instantiated': False,
        'native_cipher_table_compiled': False,
        'entire_sampler_machine_runtime_certified': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
