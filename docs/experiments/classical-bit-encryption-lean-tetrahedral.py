"""Replay concrete tetrahedral boundary zero-avoidance and normalization checks."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitTetrahedralBoundary'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['coordinate_separates_zero', 'sharpTetrahedron_face_avoids_zero',
            'sharpEdgeMidpoint_coordinates', 'sharpEdgeMidpoint_mass',
            'sharpEdgeMidpoint_normalized', 'interpolate_sharp_midpoint',
            'sharp_boundary_midpoint_nonunit', 'sharp_boundary_midpoint_normalized',
            'sharp_boundary_conditional_edge']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-tetrahedral-boundary-') as directory:
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
    modules = ['ClassicalBitTetrahedralBoundary', 'ClassicalBitNormalizedBoundary',
               'ClassicalBitSimplicialInterpolation', 'ClassicalBitBoundaryCertificate',
               'ClassicalBitConvexCertificate', 'ClassicalBitSimplexCertificate',
               'ClassicalBitRepairStability', 'ClassicalBitRepair']
    sources = [Path(__file__).resolve()] + [stem / (name + '.lean') for name in modules] + [
        ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'all_proper_tetrahedron_faces_avoid_zero': True,
        'certificate': 'a coordinate absent from the face is identically 1/6 on its convex hull',
        'actual_boundary_midpoint_interpolation_checked': True,
        'raw_midpoint_l1_mass': '2/3',
        'normalized_midpoint_coordinates': ['-1/4', '-1/4', '1/4', '1/4'],
        'raw_unit_mass_boundary_requirement_demonstrably_unnecessary': True,
        'conditional_edge_api_application_checked': True,
        'conditional_edge_application_proves_boundary_nonnullity': False,
        'concrete_boundary_nonnullity_checked': False,
        'probabilities_include_nondyadic_one_sixth': True,
        'Foundation_bounded_machine_realization_checked': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
