"""Build and audit an actual edge attaining joint distance 37/128.

The all-edge upper bound is deliberately outside this certificate's scope.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitSharpWitness'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['sharpTableChain_valid', 'sharpTableChain_edge',
            'sharpTableChain_count_distance', 'sharpTableChain_jointTV']


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    prior = ROOT / 'docs/experiments/classical-bit-encryption-lean-eight-bit-boundary.json'
    sources = dict(json.loads(prior.read_text())['source_sha256'])
    for name, expected in sources.items():
        if hashlib.sha256(Path(name).read_bytes()).hexdigest() != expected:
            raise RuntimeError('Frozen boundary source changed: ' + name)
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-sharp-edge-') as directory:
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
                 ROOT / 'Foundation/Crypto/Semantics/Probability/ClassicalBitEightBitSharpWitness.lean']:
        sources[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    print(json.dumps({
        'target_module': MODULE,
        'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'edge_endpoints_in_ordered_coordinates': [[0, 8, 24], [1, 8, 25]],
        'actual_grid_edge_verified': True,
        'integer_count_distance': 148,
        'joint_TV_for_each_message': '37/128',
        'distance_retains_secret_key_label': True,
        'all_edge_upper_bound_verified_by_this_record': False,
        'unrestricted_cryptographic_security_separation': False,
        'newness_established': False,
        'source_sha256': sources,
    }, indent=2))


if __name__ == '__main__':
    main()
