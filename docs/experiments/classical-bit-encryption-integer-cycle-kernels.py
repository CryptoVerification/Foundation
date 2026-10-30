"""Audit locally generated fair kernels and the five-state ciphertext example.
The record certifies semantic laws; it does not certify native resource bounds,
move completeness, recovery improvement, or novelty.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitCycleKernels'
DECLARATIONS = ['Foundation.Probability.FiniteFairKernelCertificate.kernel', 'Foundation.Probability.FiniteFairKernelCertificate.kernel_real', 'Foundation.Probability.FiniteFairKernelCertificate.sample', 'Foundation.Probability.FiniteFairKernelCertificate.sample_law', 'Foundation.Probability.FiniteFairKernelCertificate.realizable', 'Foundation.Probability.FiniteFairKernelCertificate.bits_law', 'Foundation.Probability.FiniteFairKernelCertificate.preserve', 'Foundation.Probability.FiniteFairKernelCertificate.columns_of_preserve', 'Foundation.Probability.FiniteFairKernelCertificate.independentCounts', 'Foundation.Probability.FiniteFairKernelCertificate.independent_rows', 'Foundation.Probability.FiniteFairKernelCertificate.independent_columns', 'Foundation.Probability.IntegerKernelCycles.rowWeight', 'Foundation.Probability.IntegerKernelCycles.direction', 'Foundation.Probability.IntegerKernelCycles.cycle', 'Foundation.Probability.IntegerKernelCycles.applyCycle', 'Foundation.Probability.IntegerKernelCycles.direction_sum', 'Foundation.Probability.IntegerKernelCycles.weighted_row_sum', 'Foundation.Probability.IntegerKernelCycles.cycle_rows', 'Foundation.Probability.IntegerKernelCycles.cycle_columns', 'Foundation.Probability.IntegerKernelCycles.unchanged_row', 'Foundation.Probability.IntegerKernelCycles.unchanged_column', 'Foundation.Probability.IntegerKernelCycles.Certificate', 'Foundation.Probability.IntegerKernelCycles.nonnegative_of_corners', 'Foundation.Probability.IntegerKernelCycles.Certificate.adjust', 'Foundation.Probability.IntegerKernelCycles.Move', 'Foundation.Probability.IntegerKernelCycles.Move.sound', 'Foundation.Probability.IntegerKernelCycles.Path', 'Foundation.Probability.IntegerKernelCycles.Path.sound', 'Foundation.Probability.IntegerKernelCycles.natural', 'Foundation.Probability.IntegerKernelCycles.Certificate.natural_cast', 'Foundation.Probability.IntegerKernelCycles.Certificate.natural_rows', 'Foundation.Probability.IntegerKernelCycles.Certificate.natural_columns', 'Foundation.Probability.IntegerKernelCycles.signed', 'Foundation.Probability.IntegerKernelCycles.Certificate.ofNat', 'Foundation.Probability.IntegerKernelCycles.applyCycle_neg', 'Foundation.Probability.IntegerKernelCycles.Move.reverse', 'Foundation.Probability.IntegerKernelCycles.Path.reverse', 'Foundation.Probability.FairCycleKernel.kernel', 'Foundation.Probability.FairCycleKernel.kernel_real', 'Foundation.Probability.FairCycleKernel.distance_eq', 'Foundation.Probability.FairCycleKernel.realizable', 'Foundation.Probability.FairCycleKernel.preserve', 'Foundation.Probability.FairCycleKernel.pathKernel', 'Foundation.Probability.FairCycleKernel.path_realizable', 'Foundation.Probability.FairCycleKernel.path_preserves', 'Foundation.Probability.IntegerKernelCycles.relation_of_corners', 'Foundation.Probability.IntegerKernelCycles.Respects', 'Foundation.Probability.IntegerKernelCycles.Path.relation', 'Foundation.Probability.FairCycleKernel.support_table_nonzero', 'Foundation.Probability.FairCycleKernel.support_iff_table_nonzero', 'Foundation.Probability.FairCycleKernel.path_joint_preserves', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.base', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.seed_kernel', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.base_certificate', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.edited', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.corner00', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.corner01', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.corner10', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.corner11', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.move', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.path', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.certificate', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.kernel', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.realizable', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.preserves', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.entry01', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.kernel_injective', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.base_kernel', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.base_ciphertext', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.path_respects', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.ciphertext', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.target_ciphertext', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.joint_preserves', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.CycleKernels.edit_distance', 'Foundation.Probability.IntegerKernelCycles.Certificate.mk', 'Foundation.Probability.IntegerKernelCycles.Certificate.nonnegative', 'Foundation.Probability.IntegerKernelCycles.Certificate.rows', 'Foundation.Probability.IntegerKernelCycles.Certificate.columns', 'Foundation.Probability.IntegerKernelCycles.Certificate.rec', 'Foundation.Probability.IntegerKernelCycles.Move.mk', 'Foundation.Probability.IntegerKernelCycles.Move.i', 'Foundation.Probability.IntegerKernelCycles.Move.j', 'Foundation.Probability.IntegerKernelCycles.Move.k', 'Foundation.Probability.IntegerKernelCycles.Move.l', 'Foundation.Probability.IntegerKernelCycles.Move.coefficient', 'Foundation.Probability.IntegerKernelCycles.Move.equation', 'Foundation.Probability.IntegerKernelCycles.Move.corner00', 'Foundation.Probability.IntegerKernelCycles.Move.corner01', 'Foundation.Probability.IntegerKernelCycles.Move.corner10', 'Foundation.Probability.IntegerKernelCycles.Move.corner11', 'Foundation.Probability.IntegerKernelCycles.Move.rec', 'Foundation.Probability.IntegerKernelCycles.Path.refl', 'Foundation.Probability.IntegerKernelCycles.Path.step', 'Foundation.Probability.IntegerKernelCycles.Path.trans', 'Foundation.Probability.IntegerKernelCycles.Path.rec']

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
    with tempfile.TemporaryDirectory(prefix='foundation-approximate-diagram-') as directory:
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
        'audited_theorem_count': 52,
        'audited_definition_count': 19,
        'audited_structure_count': 2,
        'audited_inductive_count': 1,
        'audited_constructor_projection_recursor_count': 21,
        'natural_weighted_columns_equivalent_to_endpoint_preservation': True,
        'local_four_corner_nonnegativity_implies_global_certificate': True,
        'edit_paths_compose_and_reverse_with_certificate': True,
        'path_endpoint_preservation_and_finite_fair_realizability': True,
        'local_support_relation_implies_joint_label_preservation': True,
        'retained_label_type_required_finite': False,
        'generic_exact_conditional_distance_formula_verified': True,
        'five_state_distinct_kernel_family_size': 95,
        'five_state_family_fair_bits_per_sample': 12,
        'five_state_family_endpoint_and_joint_ciphertext_preservation_verified': True,
        'five_state_family_distance_from_seed': '1849*r/524288, r=0,...,94',
        'native_compilation_and_runtime_for_new_family_claimed': False,
        'optimality_or_improved_recovery_error_claimed': False,
        'connectivity_of_all_integer_tables_by_these_moves_claimed': False,
        'sampler_inverse_from_reversing_table_edits_claimed': False,
        'whole_grid_compatibility_claimed': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
