"""Replay normalized-boundary and canonical-subcomplex theorems in Lean."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitNormalizedBoundary'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['normalized_boundary_forces_zero', 'interpolate_inclusion',
            'interpolate_ne_zero_of_face_hulls', 'normalized_subcomplex_forces_zero',
            'normalized_subcomplex_perfect_edge', 'normalized_subcomplex_approximate_edge',
            'normalized_cone_perfect_edge', 'normalized_cone_approximate_edge']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-normalized-boundary-') as directory:
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
    modules = ['ClassicalBitNormalizedBoundary', 'ClassicalBitSimplicialInterpolation',
               'ClassicalBitBoundaryCertificate', 'ClassicalBitConvexCertificate',
               'ClassicalBitSimplexCertificate', 'ClassicalBitRepairStability', 'ClassicalBitRepair']
    sources = [Path(__file__).resolve()] + [stem / (name + '.lean') for name in modules] + [
        ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'boundary_raw_l1_mass_required_to_equal_one': False,
        'normalized_boundary_condition_checked': True,
        'subcomplex_inclusion_and_boundary_matching_derived': True,
        'zero_avoidance_required_only_as_local_boundary_face_hull_condition': True,
        'separate_global_boundary_equality_required': False,
        'boundary_nonnullity_remains_explicit_premise': True,
        'perfect_edge_joint_TV_lower_bound': '2/3',
        'approximate_edge_internal_TV_lower_bound': 'margin/3',
        'concrete_boundary_nonnullity_checked': False,
        'Foundation_bounded_machine_realization_checked': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
