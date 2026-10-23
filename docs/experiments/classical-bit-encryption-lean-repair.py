"""Replay the targeted Lean build and inspect the axioms of its main results."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair'
PREFIX = MODULE + '.'
THEOREMS = [
    'mass_lower_of_correctness', 'repair_margin', 'repair_margin_bound',
    'repair_fixed', 'repairedCipher_sound', 'continuous_repairedCipher',
    'continuous_perfect_implementation',
]


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-classical-repair-') as directory:
        probe = Path(directory) / 'AxiomProbe.lean'
        probe.write_text('import ' + MODULE + '\n' + ''.join(
            '#print axioms ' + PREFIX + name + '\n' for name in THEOREMS))
        output = run(['lake', 'env', 'lean', str(probe)])
    axioms = {}
    for name in THEOREMS:
        pattern = re.escape("'" + PREFIX + name + "'") + r' depends on axioms:\s*\[([^\]]*)\]'
        match = re.search(pattern, output)
        if not match:
            raise RuntimeError('Missing axiom result for ' + name + ': ' + output)
        axioms[name] = sorted(x.strip() for x in match.group(1).split(',') if x.strip())
        unexpected = set(axioms[name]) - {'propext', 'Classical.choice', 'Quot.sound'}
        if unexpected:
            raise RuntimeError('Unexpected axioms: ' + repr(unexpected))
    sources = [Path(__file__).resolve(), ROOT / (MODULE.replace('.', '/') + '.lean'),
               ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    record = {
        'target_module': MODULE,
        'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_theorem': axioms,
        'sorry_or_additional_axioms_in_listed_theorems': False,
        'finite_key_type_is_arbitrary': True,
        'key_averaged_correctness_supported': True,
        'actual_stochastic_matrix_privacy_and_correctness_checked': True,
        'continuous_signed_repair_and_weighted_implementation_checked': True,
        'sphere_classification_checked': False,
        'topological_nonextension_checked': False,
        'quantitative_repair_distance_checked_in_Lean': False,
        'Foundation_bounded_machine_realization_checked': False,
        'newness_established': False,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
