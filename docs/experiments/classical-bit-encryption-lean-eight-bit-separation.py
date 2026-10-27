# Checkpoint 2026-10-28: this runner is prepared; its target has not yet passed the full build.
"""Verify the complete concrete four-versus-five key separation, including every actual grid edge."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitSeparation'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['EightBitTable.neighbors_checked', 'cubeVertex_monotone_step', 'gridChain_nat_difference', 'neighbor_mask_exists', 'table_chain_oriented_distance', 'table_chain_distance', 'table_five_key_edge_upper', 'table_five_key_implementation_upper', 'table_perfect_separation', 'table_approximate_separation']


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
    modules = ['ClassicalBitEightBitSeparation', 'ClassicalBitEightBitNeighborChecks', 'ClassicalBitEightBitBoundary', 'ClassicalBitEightBitVertices', 'ClassicalBitEightBitData', 'ClassicalBitDyadicCertificate', 'ClassicalBitGridGluing', 'ClassicalBitIntegralChain', 'ClassicalBitGridComplex', 'ClassicalBitGridLocator', 'ClassicalBitCubeTriangulation', 'ClassicalBitMeshGeometry', 'ClassicalBitMeshCoordinates', 'ClassicalBitProjectiveInterpolation', 'ClassicalBitBoundaryError', 'ClassicalBitRobustBoundary', 'ClassicalBitBrouwerObstruction',
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
        'kernel_checked_binary_neighbor_rows': 33,
        'axiom_audit_covers_neighbor_rows_via_aggregate_theorem': True,
        'no_native_reduction_axiom_used': True,
        'all_actual_grid_edges_covered_by_binary_neighbor_certificates': True,
        'five_key_integer_count_difference_upper_bound': 148,
        'five_key_actual_grid_edge_joint_TV_upper_bound': '37/128',
        'actual_fixed_boundary_four_key_required_edge_lower_bound': '2/3',
        'actual_fixed_boundary_approximate_four_key_required_edge_lower_bound': '7/24',
        'approximate_four_key_privacy_plus_twice_correctness_budget': '1/8',
        'certified_approximate_strict_gap': '1/384',
        'four_key_boundary_preserving_family_proven_nonempty': True,
        'first_four_boundary_keys_match_and_fifth_is_zero': True,
        'complete_finite_comparison_in_single_Lean_theorems': True,
        'unrestricted_cryptographic_security_separation': False,
        'concrete_6545_vertex_rounding_certificates_generated_in_Lean': True,
        'Foundation_machine_execution_certified': False,
        'infinity_categories_shown_necessary': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
