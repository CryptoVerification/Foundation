"""Verify every N=32 eight-bit vertex and the nonvacuous fixed-boundary four-key lower bound."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitBoundary'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['EightBitTable.vertexRow_0_checked', 'EightBitTable.vertexRow_1_checked', 'EightBitTable.vertexRow_2_checked', 'EightBitTable.vertexRow_3_checked', 'EightBitTable.vertexRow_4_checked', 'EightBitTable.vertexRow_5_checked', 'EightBitTable.vertexRow_6_checked', 'EightBitTable.vertexRow_7_checked', 'EightBitTable.vertexRow_8_checked', 'EightBitTable.vertexRow_9_checked', 'EightBitTable.vertexRow_10_checked', 'EightBitTable.vertexRow_11_checked', 'EightBitTable.vertexRow_12_checked', 'EightBitTable.vertexRow_13_checked', 'EightBitTable.vertexRow_14_checked', 'EightBitTable.vertexRow_15_checked', 'EightBitTable.vertexRow_16_checked', 'EightBitTable.vertexRow_17_checked', 'EightBitTable.vertexRow_18_checked', 'EightBitTable.vertexRow_19_checked', 'EightBitTable.vertexRow_20_checked', 'EightBitTable.vertexRow_21_checked', 'EightBitTable.vertexRow_22_checked', 'EightBitTable.vertexRow_23_checked', 'EightBitTable.vertexRow_24_checked', 'EightBitTable.vertexRow_25_checked', 'EightBitTable.vertexRow_26_checked', 'EightBitTable.vertexRow_27_checked', 'EightBitTable.vertexRow_28_checked', 'EightBitTable.vertexRow_29_checked', 'EightBitTable.vertexRow_30_checked', 'EightBitTable.vertexRow_31_checked', 'EightBitTable.vertexRow_32_checked', 'EightBitTable.vertices_checked', 'table_vertex_checked', 'table_boundary_iff', 'table_raw_grid', 'table_boundary_error', 'table_four_key_obstruction', 'table_approximate_four_key_obstruction', 'table_boundary_counts_valid', 'table_five_boundary_correspondence', 'table_four_witness_boundary', 'table_four_boundary_realizable']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-boundary-error-') as directory:
        probe = Path(directory) / 'AxiomProbe.lean'
        probe.write_text('import ' + MODULE + '\n' + ''.join(
            '#print axioms ' + NAMESPACE + name + '\n' for name in THEOREMS))
        output = run(['lake', 'env', 'lean', str(probe)])
    axioms = {}
    for name in THEOREMS:
        quoted = re.escape("'" + NAMESPACE + name + "'")
        match = re.search(quoted + r' depends on axioms:\s*\[([^\]]*)\]', output)
        if match:
            axioms[name] = sorted(x.strip() for x in match.group(1).split(',') if x.strip())
        elif re.search(quoted + r' does not depend on any axioms', output):
            axioms[name] = []
        else:
            raise RuntimeError('Missing axiom result for ' + name + ': ' + output)
        unexpected = set(axioms[name]) - {'propext', 'Classical.choice', 'Quot.sound'}
        if unexpected:
            raise RuntimeError('Unexpected axioms: ' + repr(unexpected))
    stem = ROOT / 'Foundation/Crypto/Semantics/Probability'
    modules = ['ClassicalBitEightBitBoundary', 'ClassicalBitEightBitVertices', 'ClassicalBitEightBitData', 'ClassicalBitDyadicCertificate', 'ClassicalBitGridGluing', 'ClassicalBitIntegralChain', 'ClassicalBitGridComplex', 'ClassicalBitGridLocator', 'ClassicalBitCubeTriangulation', 'ClassicalBitMeshGeometry', 'ClassicalBitMeshCoordinates', 'ClassicalBitProjectiveInterpolation', 'ClassicalBitBoundaryError', 'ClassicalBitRobustBoundary', 'ClassicalBitBrouwerObstruction',
               'ClassicalBitTetrahedralBoundary', 'ClassicalBitNormalizedBoundary',
               'ClassicalBitSimplicialInterpolation', 'ClassicalBitBoundaryCertificate',
               'ClassicalBitConvexCertificate', 'ClassicalBitSimplexCertificate',
               'ClassicalBitRepairStability', 'ClassicalBitRepair']
    vendor = ROOT / 'Foundation/ThirdParty/Brouwer'
    sources = [Path(__file__).resolve()] + [stem / (name + '.lean') for name in modules] + [
        vendor / name for name in ['Scarf.lean', 'PathComponents.lean', 'ScarfPath.lean',
                                  'Brouwer.lean', 'LICENSE', 'ORIGIN.json']] + [
        ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    sources += [ROOT / 'docs/experiments/classical-bit-encryption-lean-eight-bit-data.py',
                ROOT / 'docs/experiments/classical-bit-encryption-mesh-separation.py']
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'grid_size': 32,
        'vertex_settings_in_generated_table': 6545,
        'kernel_checked_vertex_rows': 33,
        'no_native_reduction_axiom_used': True,
        'all_vertex_five_key_cipher_mass_and_bias_checked': True,
        'boundary_fifth_key_zero_checked': True,
        'boundary_integer_rounding_certificates_checked': True,
        'actual_grid_fixed_boundary_four_key_lower_bound': '2/3',
        'actual_grid_fixed_boundary_approximate_four_key_lower_bound': '7/24',
        'approximate_four_key_privacy_plus_twice_correctness_budget': '1/8',
        'four_key_boundary_preserving_family_proven_nonempty': True,
        'entire_five_key_edge_upper_bound_checked_in_this_record': False,
        'concrete_6545_vertex_rounding_certificates_generated_in_Lean': True,
        'Foundation_machine_execution_certified': False,
        'infinity_categories_shown_necessary': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
