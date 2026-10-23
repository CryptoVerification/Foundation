"""Replay zero-hull witness extraction and its local edge-distance consequences."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitConvexCertificate'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['restore_firstThree', 'zero_convex_hull_three_small', 'zero_convex_hull_small',
            'small_unit_barycenter_pair', 'zero_convex_hull_jump',
            'perfect_convex_hull_jump', 'approximate_convex_hull_jump',
            'perfect_cell_edge_jump', 'approximate_cell_edge_jump']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-convex-certificate-') as directory:
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
    sources = [Path(__file__).resolve(), stem / 'ClassicalBitConvexCertificate.lean',
               stem / 'ClassicalBitSimplexCertificate.lean', stem / 'ClassicalBitRepairStability.lean',
               stem / 'ClassicalBitRepair.lean', ROOT / 'lakefile.toml',
               ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'four_coordinate_zero_sum_space_reduced_to_three_dimensions': True,
        'selected_original_points_at_most': 4,
        'user_supplied_four_points_and_barycentric_coefficients_required': False,
        'local_cell_zero_in_convex_hull_remains_a_premise': True,
        'adjacency_inferred_from_single_cell_pairwise_edge_condition': True,
        'whole_table_hull_substituted_for_single_cell_hull': False,
        'perfect_joint_TV_edge_lower_bound': '2/3',
        'approximate_internal_TV_edge_lower_bound': 'margin/3',
        'noncomputable_existence_uses_mathlib_Caratheodory': True,
        'boundary_nonextension_or_boundary_to_zero_cell_checked': False,
        'Foundation_bounded_machine_realization_checked': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
