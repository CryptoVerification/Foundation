"""Replay the quantitative Lean proof and inspect its principal axiom dependencies."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepairStability'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['parts_distance', 'normalized_distance_mul', 'repair_distance_mul',
            'contrast_distance_le_joint', 'perfect_jointTV', 'repairedCipher_stable']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-repair-stability-') as directory:
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
               ROOT / 'Foundation/Crypto/Semantics/Probability/ClassicalBitRepair.lean',
               ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    print(json.dumps({
        'target_module': MODULE,
        'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'finite_key_type_is_arbitrary': True,
        'metric': 'maximum over the two messages of joint key/ciphertext total variation',
        'margin_premise': 'each cipher has privacy_TV + 2*key_averaged_correctness_error <= 1-margin',
        'quantitative_conclusion': 'repaired_joint_TV <= 2*original_internal_TV/margin',
        'signed_to_actual_joint_distribution_distance_identity_checked': True,
        'attacker_without_key_advantage_identified_with_internal_metric': False,
        'topological_nonextension_checked': False,
        'finite_boundary_obstruction_checked': False,
        'Foundation_bounded_machine_realization_checked': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))


if __name__ == '__main__':
    main()
