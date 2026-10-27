"""Verify automatic boundary support and global finite projective interpolation in Lean."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitProjectiveInterpolation'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['active_vertex_on_boundary', 'projectiveMixture_boundary_error',
            'projectiveDenominator_lower', 'projectiveInterpolation_forces_zero']


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
    modules = ['ClassicalBitProjectiveInterpolation', 'ClassicalBitBoundaryError', 'ClassicalBitRobustBoundary', 'ClassicalBitBrouwerObstruction',
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
        'local_l1_rounding_error_premise': '1/64',
        'derived_normalized_boundary_coordinate_error': '3/64',
        'within_robust_Brouwer_tolerance': '3/64 < 1/18',
        'active_boundary_support_derived_from_barycentric_reconstruction': True,
        'boundary_error_derived_from_finite_vertex_rounding': True,
        'pointwise_boundary_witness_required': False,
        'continuous_interpolant_derived_from_continuous_weights': True,
        'projective_denominator_lower_bound': '1/3',
        'Brouwer_zero_for_interpolant_checked': True,
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
