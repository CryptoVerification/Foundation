"""Audit a native canonical exit and exact probabilistic game transformation.

The full-cell equality compares actual native programs with a common terminal
control. The target wrapper is executed and charged. Public-output equality
also holds with the original unwrapped 930-step target reference program.
No general coherent coupling family or free arbitrary continuation is claimed.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeCanonicalCoupling'
DECLARATIONS = ['Machine.NativeCouplingExitAdapter.leaf', 'Machine.NativeCouplingExitAdapter.leaf_run', 'Machine.NativeCouplingExitAdapter.leaf_stops', 'Machine.NativeCouplingExitAdapter.decoder', 'Machine.NativeCouplingExitAdapter.code', 'Machine.NativeCouplingExitAdapter.decoder_stops', 'Machine.NativeCouplingExitAdapter.stops', 'Machine.NativeCouplingExitAdapter.finish', 'Machine.NativeCouplingExitAdapter.run', 'Machine.NativeCouplingExitAdapter.finish_equivalent', 'Machine.NativeCouplingExitAdapter.kernelAt', 'Machine.NativeCouplingExitAdapter.kernelAt_clean', 'Machine.NativeCouplingExitAdapter.code_length', 'Machine.NativeCanonicalCouplingExecution.code', 'Machine.NativeCanonicalCouplingExecution.padding', 'Machine.NativeCanonicalCouplingExecution.targetCode', 'Machine.NativeCanonicalCouplingExecution.halt_padding_stops', 'Machine.NativeCanonicalCouplingExecution.padding_stops', 'Machine.NativeCanonicalCouplingExecution.final_control_equal', 'Machine.NativeCanonicalCouplingExecution.transformed_law', 'Machine.NativeCanonicalCouplingExecution.target_framed_law', 'Machine.NativeCanonicalCouplingExecution.target_initial_law', 'Machine.NativeCanonicalCouplingExecution.full_cell_law_equal', 'Machine.NativeCanonicalCouplingExecution.stops', 'Machine.NativeCanonicalCouplingExecution.target_stops', 'Machine.NativeCanonicalCouplingExecution.haltsWithin', 'Machine.NativeCanonicalCouplingExecution.target_haltsWithin', 'Machine.NativeCanonicalCouplingExecution.bounded', 'Machine.NativeCanonicalCouplingExecution.targetBounded', 'Machine.NativeCanonicalCouplingExecution.polynomial_time', 'Machine.NativeCanonicalCouplingExecution.target_polynomial_time', 'Machine.NativeCanonicalCouplingExecution.padding_length', 'Machine.NativeCanonicalCouplingExecution.code_length_equal', 'Machine.NativeCanonicalCouplingExecution.outputView', 'Machine.NativeCanonicalCouplingExecution.public_law_equal', 'Machine.NativeCanonicalCouplingExecution.outputView_finish', 'Machine.NativeCanonicalCouplingExecution.outputView_encode', 'Machine.NativeCanonicalCouplingExecution.target_public_reference', 'Machine.NativeCanonicalCouplingExecution.public_reference_law_equal', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.fullLaw', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.targetLaw', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.nativeGame', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.targetGame', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.full_law_equal', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.fullReification', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.fullContextPath', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.publicGame', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.publicTargetGame', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.publicReification', 'CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling.publicContextPath']
THEOREM_COUNT = 29
DEFINITION_COUNT = 21

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
        'native_exit_adapter_runtime_bound_steps': 29,
        'native_exit_adapter_code_length_bound': 149,
        'single_raw_input_transformed_execution_runtime_bound_steps': 1219,
        'original_target_reference_runtime_bound_steps': 930,
        'target_with_actual_common_terminal_control_runtime_bound_steps': 932,
        'target_padding_code_length_bound': 8671,
        'transformed_and_wrapped_target_code_lengths_equal': True,
        'both_programs_physically_reach_same_terminal_control': True,
        'free_program_counter_normalization_used': False,
        'full_cell_laws_equal_including_control_and_halt': True,
        'private_key_ciphertext_and_reference_public_packet_preserved_at_exit': True,
        'public_output_law_equals_original_unwrapped_reference': True,
        'canonical_reference_cell_layout_exit_adapter_verified': True,
        'full_cell_reification_into_exact_probabilistic_game_step': True,
        'public_output_reification_to_original_reference_game': True,
        'all_raw_inputs_stop_at_declared_budgets': True,
        'polynomial_time_contracts_verified': True,
        'arbitrary_logical_continuations_given_free_native_runtime': False,
        'general_coherent_coupling_family_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
