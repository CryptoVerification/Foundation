"""Verify integer dyadic cipher certificates and exact boundary rounding transport."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitDyadicCertificate'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['dyadic_l1_exact', 'dyadic_jointTV_exact', 'eight_bit_jointTV_le',
            'integer_rounding_coordinate_error', 'eight_bit_rounding_l1',
            'normalizeSigned_div_pos', 'gridVertexPosition_numerator',
            'sharpAffine_grid_numerator', 'normalizeSigned_grid_numerator',
            'grid_boundary_integer_error']


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
    modules = ['ClassicalBitDyadicCertificate', 'ClassicalBitGridGluing', 'ClassicalBitIntegralChain', 'ClassicalBitGridComplex', 'ClassicalBitGridLocator', 'ClassicalBitCubeTriangulation', 'ClassicalBitMeshGeometry', 'ClassicalBitMeshCoordinates', 'ClassicalBitProjectiveInterpolation', 'ClassicalBitBoundaryError', 'ClassicalBitRobustBoundary', 'ClassicalBitBrouwerObstruction',
               'ClassicalBitTetrahedralBoundary', 'ClassicalBitNormalizedBoundary',
               'ClassicalBitSimplicialInterpolation', 'ClassicalBitBoundaryCertificate',
               'ClassicalBitConvexCertificate', 'ClassicalBitSimplexCertificate',
               'ClassicalBitRepairStability', 'ClassicalBitRepair']
    vendor = ROOT / 'Foundation/ThirdParty/Brouwer'
    sources = [Path(__file__).resolve()] + [stem / (name + '.lean') for name in modules] + [
        vendor / name for name in ['Scarf.lean', 'PathComponents.lean', 'ScarfPath.lean',
                                  'Brouwer.lean', 'LICENSE', 'ORIGIN.json']] + [
        ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'signed_integer_mass_and_bias_construct_perfect_cipher': True,
        'integer_l1_difference_equals_actual_joint_TV_times_2D': True,
        'eight_bit_integer_difference_148_implies_joint_TV_le_37_over_128': True,
        'integer_cross_products_imply_rounding_error_verified': True,
        'grid_affine_raw_integer_numerator_relation_verified': True,
        'integer_vertex_error_certificate_to_actual_normalized_boundary_verified': True,
        'concrete_table_values_checked_in_this_record': False,
        'concrete_6545_vertex_rounding_certificates_generated_in_Lean': False,
        'Foundation_machine_execution_certified': False,
        'infinity_categories_shown_necessary': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
