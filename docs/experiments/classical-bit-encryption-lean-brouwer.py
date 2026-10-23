"""Replay a concrete tetrahedral obstruction, including its prior-work Brouwer dependency."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitBrouwerObstruction'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['Brouwer'] + [NAMESPACE + name for name in [
    'positive_negative_of_zero_sum', 'negative_coordinate', 'sharpAffine_ne_zero_at_boundary',
    'sharp_normalized_extension_forces_zero', 'sharpTetrahedron_entry',
    'sharpAffine_eq_weighted_labels', 'sharpAffine_bias', 'sharpAffine_center_zero',
    'sharp_parameterized_perfect_edge', 'sharp_parameterized_approximate_edge']]


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    vendor = ROOT / 'Foundation/ThirdParty/Brouwer'
    origin = json.loads((vendor / 'ORIGIN.json').read_text())
    vendor_sources = []
    for name, hashes in origin['files'].items():
        path = vendor / name
        source = path.read_text()
        assert hashlib.sha256(source.encode()).hexdigest() == hashes['local_sha256']
        restored = source.split('-/\n', 1)[1].replace(
            'import Foundation.ThirdParty.Brouwer.', 'import Gametheory.')
        assert hashlib.sha256(restored.encode()).hexdigest() == hashes['original_sha256']
        vendor_sources.append(path)
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-brouwer-obstruction-') as directory:
        probe = Path(directory) / 'AxiomProbe.lean'
        probe.write_text('import ' + MODULE + '\n' + ''.join(
            '#print axioms ' + name + '\n' for name in THEOREMS) +
            '\nexample (f : stdSimplex ℝ (Fin 4) → stdSimplex ℝ (Fin 4))\n'
            '    (hf : Continuous f) : ∃ x, f x = x := Brouwer (n := (4 : ℕ+)) f hf\n')
        output = run(['lake', 'env', 'lean', str(probe)])
    axioms = {}
    for name in THEOREMS:
        quoted = re.escape("'" + name + "'")
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
    modules = ['ClassicalBitBrouwerObstruction', 'ClassicalBitTetrahedralBoundary',
               'ClassicalBitNormalizedBoundary', 'ClassicalBitSimplicialInterpolation',
               'ClassicalBitBoundaryCertificate', 'ClassicalBitConvexCertificate',
               'ClassicalBitSimplexCertificate', 'ClassicalBitRepairStability', 'ClassicalBitRepair']
    sources = [Path(__file__).resolve()] + [stem / (name + '.lean') for name in modules] + [
        ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json',
        vendor / 'LICENSE', vendor / 'ORIGIN.json'] + vendor_sources
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'prior_work': {'repository': origin['repository'], 'commit': origin['commit'],
                       'license': origin['license'], 'only_import_paths_and_headers_changed': True,
                       'brouwer_standard_simplex_statement_checked': True},
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'concrete_domain': 'standard real three-simplex on four vertices',
        'boundary': 'normalized four-key affine labels, coordinate 1/6 - (2/3)*x_i',
        'concrete_extension_has_zero_without_nonnullity_premise': True,
        'affine_boundary_matches_original_cipher_labels': True,
        'explicit_admissible_affine_map_and_center_zero_checked': True,
        'perfect_edge_joint_TV_lower_bound': '2/3',
        'approximate_edge_internal_TV_lower_bound': 'margin/3',
        'continuous_mesh_parameterization_and_boundary_agreement_remain_premises': True,
        'concrete_refined_mesh_parameterization_constructed': False,
        'nullhomotopy_to_extension_bridge_or_Nullhomotopic_negation_checked': False,
        'Foundation_bounded_machine_realization_checked': False,
        'infinity_categories_shown_necessary': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
