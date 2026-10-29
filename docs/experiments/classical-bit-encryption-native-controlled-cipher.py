"""Audit native fair randomness, private result placement and input-controlled cipher.

This checks exact observed laws at explicitly formatted configurations.
It does not assert a raw initial-input law or polynomial compiler size.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Machine.NativeControlledEightBitCipher'
THEOREMS = ['Machine.NativeUniformSequence.code_length', 'Machine.NativeUniformSequence.run', 'Machine.NativeUniformSequence.stops', 'Machine.NativeBitGenerator.afterRead_blankBlock', 'Machine.NativeBitGenerator.blankBlock_written_move', 'Machine.NativeBitGenerator.preload_moveLeft_cons', 'Machine.NativeBitGenerator.coin_run', 'Machine.NativeBitGenerator.coin_stops', 'Machine.NativeBitGenerator.back_run', 'Machine.NativeBitGenerator.back_stops', 'Machine.NativeBitGenerator.code_length', 'Machine.NativeBitGenerator.code_stops', 'Machine.NativeBitGenerator.run', 'Machine.NativeBitDecoderTotal.stops_mono', 'Machine.NativeBitDecoderTotal.blank_run', 'Machine.NativeBitDecoderTotal.compile_stops_everywhere', 'Machine.NativeBitDecoderTotal.private_payload_stops_everywhere', 'Machine.NativeRandomPrivateResult.code_stops', 'Machine.NativeRandomPrivateResult.code_length_bound', 'Machine.NativeRandomPrivateResult.run', 'Machine.NativeRandomPrivateResult.observe_finish', 'Machine.NativeRandomPrivateResult.observed_run', 'Machine.NativeRandomPrivateResult.haltsWithin', 'Machine.NativeRandomPrivateResult.polynomial_time', 'Machine.NativeRandomPrivateResult.eight_bit_stops', 'Machine.NativeRandomPrivateResult.eight_bit_code_length_bound', 'Machine.NativeEightBitCipher.decode_encodeKey', 'Machine.NativeEightBitCipher.observe_control', 'Machine.NativeEightBitCipher.law', 'Machine.NativeEightBitCipher.stops', 'Machine.NativeEightBitCipher.haltsWithin', 'Machine.NativeEightBitCipher.polynomial_time', 'Machine.NativeEightBitCipher.code_length_bound', 'Machine.EightBitCipherControl.block_request', 'Machine.EightBitCipherControl.parseRequest_request', 'Machine.NativeControlledEightBitCipher.halt_stops', 'Machine.NativeControlledEightBitCipher.leaves_stops', 'Machine.NativeControlledEightBitCipher.leaves_length_bound', 'Machine.NativeControlledEightBitCipher.code_def', 'Machine.NativeControlledEightBitCipher.code_stops', 'Machine.NativeControlledEightBitCipher.code_length_bound', 'Machine.NativeControlledEightBitCipher.leaves_request', 'Machine.NativeControlledEightBitCipher.law', 'Machine.NativeControlledEightBitCipher.haltsWithin', 'Machine.NativeControlledEightBitCipher.polynomial_time']


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
        'one_fixed_native_program_for_all_control_points_and_messages': True,
        'native_fair_random_bit_count': 8,
        'control_input_bit_count': 19,
        'private_key_bit_count': 3,
        'ciphertext_output_bit_count': 1,
        'exact_formatted_entry_observation_law_verified': True,
        'observation': 'joint key label and ciphertext; includes secret key',
        'random_generator_runtime_bound': '7*n+1',
        'random_generator_code_length': '11*n+1',
        'fixed_payload_runtime_bound': '10*n+11',
        'fixed_eight_bit_payload_runtime_bound': 91,
        'common_controlled_program_runtime_bound': 148,
        'common_program_code_length_bound': 'code.length+6 <= 3932*2^19',
        'code_size_polynomial_in_control_width_claimed': False,
        'all_raw_inputs_termination_verified': True,
        'raw_initial_input_observation_law_verified': False,
        'formatted_entry_requires_reserved_private_and_output_cells': True,
        'control_and_coin_history_retained_privately': True,
        'arbitrary_full_tape_caller_distance_bound_verified': False,
        'continuing_caller_integration_verified': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
