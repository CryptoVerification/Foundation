"""Verify integer support transfer and width-one chain functionals for common-face geometry."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitIntegralChain'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['integral_support_le', 'integral_support_ge', 'cubeAxisOrder_bijective',
            'cubeVertex_order_coordinate', 'cubeVertex_sorted', 'cube_difference_one_sided',
            'cube_difference_width', 'cube_binary_member', 'integral_chain_region_member',
            'integral_average_le', 'integral_average_ge', 'gridIntegralCoordinate_injective',
            'gridChain_integral_coordinate', 'gridChain_coordinate_width',
            'gridChain_difference_width', 'gridChain_region_member']


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
    modules = ['ClassicalBitIntegralChain', 'ClassicalBitGridComplex', 'ClassicalBitGridLocator', 'ClassicalBitCubeTriangulation', 'ClassicalBitMeshGeometry', 'ClassicalBitMeshCoordinates', 'ClassicalBitProjectiveInterpolation', 'ClassicalBitBoundaryError', 'ClassicalBitRobustBoundary', 'ClassicalBitBrouwerObstruction',
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
        'integer_width_one_average_to_active_support_inequalities_verified': True,
        'cube_coordinate_differences_have_width_one_verified': True,
        'binary_points_in_chain_order_region_are_chain_vertices_verified': True,
        'translated_integer_chain_region_membership_verified': True,
        'actual_grid_chain_integer_coordinate_width_verified': True,
        'actual_grid_chain_integer_difference_width_verified': True,
        'actual_table_vertex_region_to_chain_membership_verified': True,
        'global_common_face_geometry_Lean_verified': False,
        'geometric_mesh_locator_and_continuity_Lean_verified': False,
        'concrete_6545_vertex_rounding_certificates_generated_in_Lean': False,
        'Foundation_machine_execution_certified': False,
        'infinity_categories_shown_necessary': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
