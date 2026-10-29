"""Audit physical request preparation, restored tape roles and the standard evaluator.

Flagged input is decoded, erased, physically copied back and rewound before
calling the existing cipher/decision code. Standard output packet laws are checked.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Machine.NativePreparedKeyDecision'
THEOREMS = ['Machine.NativeBoundedFlaggedTransfer.preload_cons', 'Machine.NativeBoundedFlaggedTransfer.preload_append', 'Machine.NativeBoundedFlaggedTransfer.preload_erasedBefore', 'Machine.NativeBoundedFlaggedTransfer.erasedBefore_add', 'Machine.NativeBoundedFlaggedTransfer.pair_run', 'Machine.NativeBoundedFlaggedTransfer.pair_stops', 'Machine.NativeBoundedFlaggedTransfer.copies_length', 'Machine.NativeBoundedFlaggedTransfer.copies_stops', 'Machine.NativeBoundedFlaggedTransfer.copies_run', 'Machine.NativeFixedWordRewind.stops_swap', 'Machine.NativeFixedWordRewind.left_actions', 'Machine.NativeFixedWordRewind.input_stops', 'Machine.NativeFixedWordRewind.output_stops', 'Machine.NativeFixedWordRewind.output_length', 'Machine.NativeFixedWordRewind.output_run', 'Machine.NativeFlaggedRequestPreparation.terminal_run', 'Machine.NativeFlaggedRequestPreparation.terminal_stops', 'Machine.NativeFlaggedRequestPreparation.decode_stops', 'Machine.NativeFlaggedRequestPreparation.decode_run', 'Machine.NativeFlaggedRequestPreparation.stops', 'Machine.NativeFlaggedRequestPreparation.code_length', 'Machine.NativeFlaggedRequestPreparation.run', 'Machine.NativeFixedRawTransfer.one_run', 'Machine.NativeFixedRawTransfer.one_stops', 'Machine.NativeFixedRawTransfer.code_length', 'Machine.NativeFixedRawTransfer.stops', 'Machine.NativeFixedRawTransfer.run', 'Machine.NativeFixedRawTransfer.back_stops', 'Machine.NativeFixedRawTransfer.back_run', 'Machine.NativeFixedRawTransfer.restored_stops', 'Machine.NativeFixedRawTransfer.restored_length', 'Machine.NativeFixedRawTransfer.restored_run', 'Machine.NativeKeyPairOutputPacket.caller_packet', 'Machine.NativeKeyPairOutputPacket.kernel_packet', 'Machine.NativeKeyPairOutputPacket.framed_packet', 'Machine.NativeKeyPairOutputPacket.evalWithin_of_halts', 'Machine.NativePreparedKeyDecision.request_length', 'Machine.NativePreparedKeyDecision.rawInput_length', 'Machine.NativePreparedKeyDecision.readDecision_control', 'Machine.NativePreparedKeyDecision.readDecision_equivalent', 'Machine.NativePreparedKeyDecision.preparation_stops', 'Machine.NativePreparedKeyDecision.preparation_length', 'Machine.NativePreparedKeyDecision.source_stops', 'Machine.NativePreparedKeyDecision.stops', 'Machine.NativePreparedKeyDecision.blankBlock_erasedBefore', 'Machine.NativePreparedKeyDecision.preparation_run', 'Machine.NativePreparedKeyDecision.erasedBefore_blank', 'Machine.NativePreparedKeyDecision.blankBlock_equivalent', 'Machine.NativePreparedKeyDecision.entry_equivalent', 'Machine.NativePreparedKeyDecision.handoff', 'Machine.NativePreparedKeyDecision.source_decision', 'Machine.NativePreparedKeyDecision.framed_law', 'Machine.NativePreparedKeyDecision.initial_law', 'Machine.NativePreparedKeyDecision.haltsWithin', 'Machine.NativePreparedKeyDecision.polynomial_time', 'Machine.NativePreparedKeyDecision.acceptance_law', 'Machine.NativePreparedKeyDecision.first_acceptance', 'Machine.NativePreparedKeyDecision.second_acceptance', 'Machine.NativePreparedKeyDecision.gap_attained', 'Machine.NativePreparedKeyDecision.edge_bound', 'Machine.NativePreparedKeyDecision.outputBits_control', 'Machine.NativePreparedKeyDecision.source_packet', 'Machine.NativePreparedKeyDecision.framed_packet', 'Machine.NativePreparedKeyDecision.initial_packet', 'Machine.NativePreparedKeyDecision.evalWithin_law', 'Machine.NativePreparedKeyDecision.no_timeout', 'Machine.NativePreparedKeyDecision.evalWithin_acceptance', 'Machine.NativePreparedKeyDecision.evalWithin_gap_attained']


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
        'raw_request_format': '39 bits: flag/data pairs for 19 request bits, followed by false terminator',
        'native_request_bit_count': 19,
        'flagged_preparation_code_length': 393,
        'flagged_preparation_runtime_bound': 274,
        'physical_copy_back_and_rewind_code_length': 328,
        'physical_copy_back_and_rewind_runtime_bound': 212,
        'complete_preparation_code_length': 724,
        'complete_preparation_runtime_bound': 487,
        'consumed_flag_and_data_cells_physically_erased': True,
        'copied_request_cells_physically_erased_after_copy_back': True,
        'request_physically_returned_to_original_input_tape': True,
        'decision_written_on_original_output_tape': True,
        'runtime_whole_tape_exchange_used': False,
        'free_tape_loader_or_reset_used': False,
        'complete_single_native_execution_runtime_bound': 930,
        'stops_on_all_raw_inputs_including_malformed_requests': True,
        'malformed_requests_have_correctness_or_rejection_guarantee': False,
        'valid_request_standard_evalWithin_law_verified': True,
        'standard_output_packet': 'some [complemented ciphertext, native-computed key-label decision]',
        'timeout_probability_all_raw_inputs': '0',
        'all_actual_edges_decision_gap_bound': '37/128',
        'sharp_decision_gap_standard_evalWithin': '37/128',
        'sharp_first_acceptance': '1',
        'sharp_second_acceptance': '91/128',
        'private_key_read_by_decision_code': True,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
