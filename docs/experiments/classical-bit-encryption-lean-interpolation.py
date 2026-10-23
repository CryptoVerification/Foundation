"""Replay the canonical barycentric interpolator and cone consequences in Lean."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitSimplicialInterpolation'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['interpolate_vertex', 'interpolate_bias', 'interpolate_cell', 'interpolate_cover',
            'faceEdge_iff_pair', 'cone_realization_contractible',
            'interpolated_perfect_edge', 'interpolated_approximate_edge',
            'cone_perfect_edge', 'cone_approximate_edge']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-interpolation-') as directory:
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
    modules = ['ClassicalBitSimplicialInterpolation', 'ClassicalBitBoundaryCertificate',
               'ClassicalBitConvexCertificate', 'ClassicalBitSimplexCertificate',
               'ClassicalBitRepairStability', 'ClassicalBitRepair']
    sources = [Path(__file__).resolve()] + [stem / (name + '.lean') for name in modules] + [
        ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'finite_vertices_with_abstract_faces': True,
        'canonical_realization_uses_nonnegative_normalized_coordinates': True,
        'continuous_interpolation_built_from_vertex_labels': True,
        'vertex_label_reproduction_checked': True,
        'zero_sum_preservation_checked': True,
        'single_cell_convex_cover_derived': True,
        'edge_relation_agrees_with_two_vertex_faces': True,
        'cone_contractibility_derived_from_finite_face_condition': True,
        'opaque_global_interpolator_or_cell_cover_required': False,
        'boundary_nonnullity_and_boundary_agreement_still_premises': True,
        'concrete_boundary_nonnullity_checked': False,
        'geometric_mesh_to_canonical_realization_homeomorphism_checked': False,
        'Foundation_bounded_machine_realization_checked': False,
        'infinity_categories_shown_necessary': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
