"""Verify global common-face gluing, continuous coordinates, and edge obstructions for every positive grid size."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitGridGluing'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['supported_image_width', 'grid_integer_means_eq', 'grid_chain_support_transfer',
            'orderedGridComplex_common_face', 'orderedGridComplex_meshGeometry',
            'ordered_grid_perfect_edge', 'orderedGridComplex_projection_bijective',
            'ordered_grid_weights_exist', 'ordered_grid_approximate_edge']


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
    modules = ['ClassicalBitGridGluing', 'ClassicalBitIntegralChain', 'ClassicalBitGridComplex', 'ClassicalBitGridLocator', 'ClassicalBitCubeTriangulation', 'ClassicalBitMeshGeometry', 'ClassicalBitMeshCoordinates', 'ClassicalBitProjectiveInterpolation', 'ClassicalBitBoundaryError', 'ClassicalBitRobustBoundary', 'ClassicalBitBrouwerObstruction',
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
        'active_support_transfer_between_arbitrary_valid_base_cubes_verified': True,
        'global_common_face_geometry_Lean_verified': True,
        'all_MeshGeometry_obligations_for_actual_ordered_grid_discharged': True,
        'actual_grid_projection_bijectivity_verified': True,
        'continuous_normalized_reconstructing_single_face_weights_exist': True,
        'geometric_mesh_locator_and_continuity_Lean_verified': True,
        'executable_machine_locator_certified': False,
        'perfect_actual_grid_edge_joint_TV_lower_bound': '2/3',
        'approximate_actual_grid_edge_implementation_distance_lower_bound': 'mu/3',
        'finite_boundary_rounding_certificates_still_required': True,
        'holds_for_every_positive_integer_grid_size_including_32': True,
        'concrete_6545_vertex_rounding_certificates_generated_in_Lean': False,
        'Foundation_machine_execution_certified': False,
        'infinity_categories_shown_necessary': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
