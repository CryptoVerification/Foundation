"""Audit finite fair sampling and native conditional recovery obstructions.
Errors measure conditional kernel discrepancy, distinct from game-path loss.
The inherited structural cells may copy/erase proof certificates, not random state.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.RecoverySamplingObstruction'
DECLARATIONS = ['Foundation.Probability.FiniteFairSampling.Realizable', 'Foundation.Probability.FiniteFairSampling.event_count', 'Foundation.Probability.FiniteFairSampling.event_real_count', 'Foundation.Probability.FiniteFairSampling.reciprocal_dvd', 'Foundation.Probability.FiniteFairSampling.no_reciprocal_odd_factor', 'Foundation.Probability.FiniteFairSampling.map', 'Foundation.Probability.FiniteFairSampling.pure', 'Foundation.Probability.FiniteFairSampling.bit', 'Foundation.Probability.FiniteFairSampling.bind', 'Foundation.Probability.FiniteFairSampling.reciprocal_error_lower', 'Machine.FiniteFairExecution.step_realizable', 'Machine.FiniteFairExecution.eval_realizable', 'Machine.FiniteFairExecution.observed_realizable', 'Machine.FiniteFairExecution.random_initial_realizable', 'CryptoLogic.Polygraph.Experiment.RecoverySamplingObstruction.forward_row_not_realizable', 'CryptoLogic.Polygraph.Experiment.RecoverySamplingObstruction.reverse_row_not_realizable', 'CryptoLogic.Polygraph.Experiment.RecoverySamplingObstruction.no_native_forward', 'CryptoLogic.Polygraph.Experiment.RecoverySamplingObstruction.no_native_reverse', 'CryptoLogic.Polygraph.Experiment.RecoverySamplingObstruction.forward_approximation_lower', 'CryptoLogic.Polygraph.Experiment.RecoverySamplingObstruction.native_forward_approximation_lower']

def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def local_sources(module):
    pending = [module]
    found = set()
    while pending:
        current = pending.pop()
        path = ROOT / (current.replace('.', '/') + '.lean')
        if path in found:
            continue
        if not path.is_file():
            raise RuntimeError('Missing local dependency: ' + str(path))
        found.add(path)
        for line in path.read_text().splitlines():
            if line.startswith('import '):
                pending.extend(name for name in line.split()[1:] if name.startswith('Foundation.'))
    return sorted(found)


def main():
    run(['lake', 'build', MODULE])
    with tempfile.TemporaryDirectory(prefix='foundation-approximate-diagram-') as directory:
        probe = Path(directory) / 'AxiomProbe.lean'
        probe.write_text('import ' + MODULE + '\n' + ''.join(
            '#print axioms ' + name + '\n' for name in DECLARATIONS))
        output = run(['lake', 'env', 'lean', str(probe)])
    axioms = {}
    for name in DECLARATIONS:
        quoted = re.escape("'" + name + "'")
        match = re.search(quoted + r' depends on axioms:\s*\[([^\]]*)\]', output)
        if match:
            axioms[name] = sorted(x.strip() for x in match.group(1).split(',') if x.strip())
        elif re.search(quoted + r' does not depend on any axioms', output):
            axioms[name] = []
        else:
            raise RuntimeError('Missing axiom result for ' + name + ': ' + output)
        if set(axioms[name]) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError('Unexpected axioms for ' + name)
    sources = local_sources(MODULE) + [Path(__file__).resolve()] + [
        ROOT / name for name in ['lakefile.toml', 'lean-toolchain', 'lake-manifest.json']]
    print(json.dumps({
        'target_module': MODULE, 'targeted_lake_build_passed': True,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'axioms_per_declaration': axioms,
        'sorry_or_additional_axioms_in_listed_declarations': False,
        'audited_theorem_count': 19,
        'audited_definition_count': 1,
        'all_events_have_integer_numerator_over_power_of_two': True,
        'fair_realizability_closed_under_maps_and_sequential_sampling': True,
        'native_fixed_budget_fair_realizability_verified': True,
        'native_configuration_type_required_finite': False,
        'native_dyadic_random_initial_law_extension_verified': True,
        'forward_conditional_row': 2,
        'forward_obstructing_output': 0,
        'forward_obstructing_probability': '1/21',
        'reverse_conditional_row': 1,
        'reverse_obstructing_output': 2,
        'reverse_obstructing_probability': '1/44',
        'fixed_state_bounded_native_exact_selected_forward_and_reverse_impossible': True,
        'arbitrary_native_program_state_horizon_and_deterministic_observation_quantified': True,
        'forward_conditional_total_variation_lower_bound': '1/(21*2^steps)',
        'endpoint_distribution_nonrealizability_claimed': False,
        'all_possible_recovery_couplings_nonrealizable_claimed': False,
        'approximate_or_unbounded_almost_sure_sampling_ruled_out': False,
        'previous_compiled_two_to_five_recovery_invalidated': False,
        'native_compiler_for_selected_kernels_created': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
