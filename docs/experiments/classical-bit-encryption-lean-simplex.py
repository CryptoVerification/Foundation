"""Replay local four-point jump certificates and inspect their Lean axioms."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitSimplexCertificate'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['four_weights_large', 'unit_barycenter_diameter', 'unit_barycenter_pair',
            'perfect_simplex_jump', 'approximate_simplex_jump',
            'sharpTetrahedron_barycenter', 'sharpTetrahedron_joint_bound', 'sharpTetrahedron_attains']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-simplex-certificate-') as directory:
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
    sources = [Path(__file__).resolve(), ROOT / (MODULE.replace('.', '/') + '.lean'),
               ROOT / 'Foundation/Crypto/Semantics/Probability/ClassicalBitRepairStability.lean',
               ROOT / 'Foundation/Crypto/Semantics/Probability/ClassicalBitRepair.lean',
               ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    print(json.dumps({
        'target_module': MODULE,
        'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'certificate': 'four unit signed vectors, nonnegative coefficients summing to one, zero weighted mean',
        'perfect_cipher_joint_TV_pair_lower_bound': '2/3',
        'approximate_cipher_internal_TV_pair_lower_bound': 'margin/3',
        'actual_joint_probability_distance_used': True,
        'explicit_sharp_certificate_checked': True,
        'sharp_certificate_has_nondyadic_probabilities': True,
        'zero_barycenter_extracted_from_boundary': False,
        'Caratheodory_reduction_checked': False,
        'topological_nonextension_checked': False,
        'Foundation_bounded_machine_realization_checked': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
