"""Build and audit the exact eight-fair-bit realization of the table key law.

This semantic result does not assert a Foundation machine runtime bound.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitSampler'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.'
THEOREMS = ['sampleCounts_fiber_card', 'sampleCounts_event_probability',
            'sampleCounts_bits_event_probability', 'tableNaturalCounts_sum',
            'tableSampleEightBits_probability', 'tableSampleEightBits_cipher_weight']


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
    with tempfile.TemporaryDirectory(prefix='foundation-table-sampler-') as directory:
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
                 ROOT / 'Foundation/Crypto/Semantics/Probability/ClassicalBitEightBitSampler.lean',
                 ROOT / 'Foundation/Crypto/Semantics/Probability/ClassicalBitDyadicSampler.lean',
                 ROOT / 'Foundation/Crypto/Semantics/Probability/Facts.lean',
                 ROOT / 'Foundation/Crypto/Semantics/Probability/Comp.lean']:
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
        'all_vertex_key_weights_realized_exactly': True,
        'decoder_is_computable_Lean_definition': True,
        'key_law_is_the_existing_tableFiveCipher_key_law': True,
        'Foundation_machine_execution_certified': False,
        'Foundation_machine_runtime_bound_certified': False,
        'all_edge_upper_bound_verified_by_this_record': False,
        'unrestricted_cryptographic_security_separation': False,
        'newness_established': False,
        'source_sha256': sources,
    }, indent=2))


if __name__ == '__main__':
    main()
