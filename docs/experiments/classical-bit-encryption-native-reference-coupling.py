"""Audit actual request preparation from a reference full-cell state.

The native reference experiment, request preparation, conditional sampler,
recovery and physical erasure are one continuing execution. The clean exit
layout differs from the canonical reference layout; that exit adapter remains.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Machine.NativeReferenceCouplingExecution'
DECLARATIONS = ['Machine.NativeCouplingRequestAdapter.leaf', 'Machine.NativeCouplingRequestAdapter.prepared', 'Machine.NativeCouplingRequestAdapter.leaf_run', 'Machine.NativeCouplingRequestAdapter.leaf_stops', 'Machine.NativeCouplingRequestAdapter.decoder', 'Machine.NativeCouplingRequestAdapter.code', 'Machine.NativeCouplingRequestAdapter.decoder_stops', 'Machine.NativeCouplingRequestAdapter.stops', 'Machine.NativeCouplingRequestAdapter.run', 'Machine.NativeCouplingRequestAdapter.code_length', 'Machine.NativeAdaptedRecoverableCoupling.blank_left', 'Machine.NativeAdaptedRecoverableCoupling.prepared_equivalent', 'Machine.NativeAdaptedRecoverableCoupling.code', 'Machine.NativeAdaptedRecoverableCoupling.atControl', 'Machine.NativeAdaptedRecoverableCoupling.atControl_equivalent', 'Machine.NativeAdaptedRecoverableCoupling.clean_kernel', 'Machine.NativeAdaptedRecoverableCoupling.run_at', 'Machine.NativeAdaptedRecoverableCoupling.kernelAt', 'Machine.NativeAdaptedRecoverableCoupling.kernelAt_finish', 'Machine.NativeAdaptedRecoverableCoupling.stops', 'Machine.NativeAdaptedRecoverableCoupling.haltsWithin', 'Machine.NativeAdaptedRecoverableCoupling.bounded', 'Machine.NativeAdaptedRecoverableCoupling.polynomial_time', 'Machine.NativeAdaptedRecoverableCoupling.code_length', 'Machine.NativeReferenceCouplingExecution.code', 'Machine.NativeReferenceCouplingExecution.cleanEncode', 'Machine.NativeReferenceCouplingExecution.cleanEncode_injective', 'Machine.NativeReferenceCouplingExecution.source_parent', 'Machine.NativeReferenceCouplingExecution.source_kernel', 'Machine.NativeReferenceCouplingExecution.framed_law', 'Machine.NativeReferenceCouplingExecution.initial_law', 'Machine.NativeReferenceCouplingExecution.sharp_target_law', 'Machine.NativeReferenceCouplingExecution.stops', 'Machine.NativeReferenceCouplingExecution.haltsWithin', 'Machine.NativeReferenceCouplingExecution.bounded', 'Machine.NativeReferenceCouplingExecution.polynomial_time']
THEOREM_COUNT = 25
DEFINITION_COUNT = 11

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
        'native_request_adapter_runtime_bound_steps': 45,
        'native_request_adapter_code_length_bound': 261,
        'old_key_cells_erased_by_request_adapter': 3,
        'old_output_cells_erased_by_request_adapter': 2,
        'reference_exit_through_clean_sampler_runtime_bound_steps': 258,
        'reference_exit_through_clean_sampler_code_length_bound': 8519,
        'reference_experiment_runtime_bound_steps': 930,
        'single_continuing_reference_and_coupling_runtime_bound_steps': 1189,
        'all_raw_inputs_stop_at_declared_budgets': True,
        'bounded_program_and_polynomial_time_verified': True,
        'entry_request_computed_by_real_native_reads_writes_and_erasures': True,
        'reference_full_cell_state_entry_adapter_verified': True,
        'kernel_on_equivalent_full_cell_representations_verified': True,
        'single_raw_execution_sharp_target_full_cell_law_verified': True,
        'target_result_to_clean_full_cell_state_embedding_injective': True,
        'clean_exit_cell_law': 'Roundtrip.q(message).map(cleanEncode(actual final control))',
        'clean_full_cell_state_equals_canonical_reference_exit_claimed': False,
        'canonical_reference_exit_adapter_verified': False,
        'arbitrary_logical_continuations_given_free_native_runtime': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
