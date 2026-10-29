"""Audit the complete finite eight-bit comparison, its exact maximum, and both gaps.

These are joint key/ciphertext distances, not key-hidden security advantages.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitCertifiedComparison'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['table_experiment_edge_upper', 'table_experiment_maximum_attained',
            'table_experiment_perfect_gap', 'tableEightBitImplementationDistance_eq',
            'table_experiment_approximate_gap', 'table_four_boundary_realizable',
            'tableSampleEightBits_cipher_weight', 'tableEncryptBit_correct',
            'tableEightBitLaw_atom', 'tableEightBitJointDistance_eq_jointTV']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    records = [ROOT / 'docs/experiments' / name for name in [
        'classical-bit-encryption-lean-eight-bit-separation.json',
        'classical-bit-encryption-lean-eight-bit-experiment.json',
        'classical-bit-encryption-lean-eight-bit-sharp-witness.json']]
    sources = {}
    for prior in records:
        data = json.loads(prior.read_text())
        if not data['targeted_lake_build_passed']:
            raise RuntimeError('Prerequisite was not verified: ' + str(prior))
        for name, expected in data['source_sha256'].items():
            if name in sources and sources[name] != expected:
                raise RuntimeError('Conflicting prerequisite hashes: ' + name)
            sources[name] = expected
    for name, expected in sources.items():
        if hashlib.sha256(Path(name).read_bytes()).hexdigest() != expected:
            raise RuntimeError('Frozen prerequisite source changed: ' + name)
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-certified-comparison-') as directory:
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
    for path in [Path(__file__).resolve(), *records,
                 ROOT / 'Foundation/Crypto/Semantics/Probability/ClassicalBitEightBitCertifiedComparison.lean']:
        sources[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    print(json.dumps({
        'target_module': MODULE,
        'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'grid_vertex_settings': 6545,
        'independent_uniform_bits': 8,
        'key_labels': 5,
        'exact_joint_key_ciphertext_atom_law_verified': True,
        'encryption_and_decryption_are_same_computable_involution': True,
        'all_actual_grid_edge_joint_distance_upper_bound': '37/128',
        'actual_grid_edge_attaining_upper_bound_verified': True,
        'perfect_four_key_required_edge_lower_bound': '2/3',
        'perfect_four_key_quantitative_gap': '145/384',
        'approximate_four_key_required_edge_lower_bound': '7/24',
        'approximate_privacy_plus_twice_correctness_budget': '1/8',
        'approximate_four_key_quantitative_gap': '1/384',
        'four_key_boundary_preserving_family_nonempty': True,
        'distance_retains_secret_key_label': True,
        'Foundation_machine_execution_certified': False,
        'Foundation_machine_runtime_bound_certified': False,
        'all_edge_upper_bound_verified_by_this_record': True,
        'unrestricted_cryptographic_security_separation': False,
        'newness_established': False,
        'infinity_categories_shown_necessary': False,
        'source_sha256': sources,
    }, indent=2))


if __name__ == '__main__':
    main()
