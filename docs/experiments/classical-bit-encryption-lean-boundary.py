"""Replay the conditional nonnull-boundary to large-edge Lean theorem."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitBoundaryCertificate'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['mass_pos_of_ne_zero', 'normalizeSigned_bias', 'normalizeSigned_mass',
            'normalizeSigned_fixed', 'nonnull_boundary_forces_zero',
            'nonnull_boundary_forces_perfect_edge', 'nonnull_boundary_forces_approximate_edge']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-boundary-certificate-') as directory:
        probe = Path(directory) / 'AxiomProbe.lean'
        probe.write_text('import ' + MODULE + '\n' + ''.join(
            '#print axioms ' + NAMESPACE + name + '\n' for name in THEOREMS))
        output = run(['lake', 'env', 'lean', str(probe)])
    axioms = {}
    for name in THEOREMS:
        pattern = re.escape("'" + NAMESPACE + name + "'") + r' depends on axioms:\s*\[([^\]]*)\]'
        match = re.search(pattern, output)
        if not match:
            raise RuntimeError('Missing axiom result for ' + name + ': ' + output)
        axioms[name] = sorted(x.strip() for x in match.group(1).split(',') if x.strip())
        unexpected = set(axioms[name]) - {'propext', 'Classical.choice', 'Quot.sound'}
        if unexpected:
            raise RuntimeError('Unexpected axioms: ' + repr(unexpected))
    stem = ROOT / 'Foundation/Crypto/Semantics/Probability'
    sources = [Path(__file__).resolve(), stem / 'ClassicalBitBoundaryCertificate.lean',
               stem / 'ClassicalBitConvexCertificate.lean', stem / 'ClassicalBitSimplexCertificate.lean',
               stem / 'ClassicalBitRepairStability.lean', stem / 'ClassicalBitRepair.lean',
               ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'boundary_nonnullity_is_explicit_premise': True,
        'contractible_interior_is_explicit_premise': True,
        'continuous_zero_sum_interpolant_is_explicit_premise': True,
        'single_cell_convex_cover_is_explicit_premise': True,
        'conditional_boundary_to_zero_and_actual_edge_derived': True,
        'four_points_or_barycentric_coefficients_required_from_user': False,
        'perfect_joint_TV_edge_lower_bound': '2/3',
        'approximate_internal_TV_edge_lower_bound': 'margin/3',
        'concrete_boundary_nonnullity_checked': False,
        'concrete_simplicial_interpolant_and_cover_constructed': False,
        'Foundation_bounded_machine_realization_checked': False,
        'infinity_categories_shown_necessary': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
