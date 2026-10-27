"""Verify the concrete six-tetrahedron cube cover and its ordered-coordinate tie rule."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitCubeTriangulation'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['cube_order_exists', 'cubeWeights_sum', 'cubeWeights_nonneg',
            'cube_chain_coordinate', 'cubeWeights_reconstruct', 'cube_chain_cover',
            'cubeWeights_recover', 'cube_chain_affineIndependent', 'grid_cube_chain_cover',
            'cube_stable_order_exists', 'cube_stable_sorted', 'cube_stable_chain_ordered',
            'cubeVertex_bounds', 'ordered_grid_cube_cover']


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
    modules = ['ClassicalBitCubeTriangulation', 'ClassicalBitMeshGeometry', 'ClassicalBitMeshCoordinates', 'ClassicalBitProjectiveInterpolation', 'ClassicalBitBoundaryError', 'ClassicalBitRobustBoundary', 'ClassicalBitBrouwerObstruction',
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
        'six_cube_chain_tetrahedra_defined': True,
        'all_real_cube_points_covered_in_Lean': True,
        'nonnegative_normalized_reconstructing_coefficients_derived': True,
        'each_cube_chain_affine_independent': True,
        'arbitrary_positive_scale_and_translation_cover_checked': True,
        'decreasing_axis_tie_rule_verified': True,
        'ordered_chamber_chain_preservation_verified': True,
        'ordered_grid_cube_cover_for_all_real_points_verified': True,
        'all_parameter_simplex_points_assigned_integer_grid_cells': False,
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
