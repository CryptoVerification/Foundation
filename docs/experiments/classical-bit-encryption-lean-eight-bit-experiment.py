"""Audit the exact eight-bit joint encryption experiment and its distance.

The observations retain the key. No machine execution bound is asserted.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitExperiment'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['table_signed_nonneg_iff', 'tableEncryptBit_probability',
            'tableEncryptBit_correct', 'tableEncryptBit_atom_factor',
            'tableEightBitLaw_atom', 'tableEightBitJointDistance_eq_jointTV']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    prior = ROOT / 'docs/experiments/classical-bit-encryption-lean-eight-bit-sampler.json'
    sources = dict(json.loads(prior.read_text())['source_sha256'])
    for name, expected in sources.items():
        if hashlib.sha256(Path(name).read_bytes()).hexdigest() != expected:
            raise RuntimeError('Frozen sampler source changed: ' + name)
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-table-experiment-') as directory:
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
    for path in [Path(__file__).resolve(), prior,
                 ROOT / 'Foundation/Crypto/Semantics/Probability/ClassicalBitEightBitExperiment.lean']:
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
        'finite_experiment_distance_equals_existing_joint_TV': True,
        'distance_retains_secret_key_label': True,
        'Foundation_machine_execution_certified': False,
        'Foundation_machine_runtime_bound_certified': False,
        'all_edge_upper_bound_verified_by_this_record': False,
        'unrestricted_cryptographic_security_separation': False,
        'newness_established': False,
        'source_sha256': sources,
    }, indent=2))


if __name__ == '__main__':
    main()
