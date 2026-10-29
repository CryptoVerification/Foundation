"""Audit a concrete nonidentity round trip of selected native-state kernels.

Same endpoint law and equal conservative losses do not supply a four-cell.
The counterexample concerns fixed chosen kernels, not all possible couplings.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'Foundation.Crypto.Logic.Polygraph.NativeStateRoundtrip'
DECLARATIONS = ['Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.Result', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.p', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.q', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.sourceCount', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.targetCount', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.source_count', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.target_count', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.p_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.q_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.source_supported', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.forward_residual', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.reverse_residual', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.kernel_real', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.roundtrip', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.preserves', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.changes_key', 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Roundtrip.not_identity', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.first', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.second', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.reverse_edge', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.loop', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.loop_preserves', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.loop_loss', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.kernel_encoded', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.kernel_recovered', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.source_reachable', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.changes_key', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.paddedIdentityStep', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.stationary', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.stationary_kernel', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.same_loss', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.no_cell', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.no_reverse_cell', 'CryptoLogic.Polygraph.Experiment.NativeState.RoundtripAudit.no_diagram_edits']
THEOREM_COUNT = 23
DEFINITION_COUNT = 11

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
    with tempfile.TemporaryDirectory(prefix='foundation-native-controlled-cipher-') as directory:
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
        'audited_theorem_count': THEOREM_COUNT,
        'audited_definition_count': DEFINITION_COUNT,
        'native_machine_runtime_bound_steps': 930,
        'native_code_changed': False,
        'grid_vertices': [[0, 8, 24], [1, 8, 25]],
        'outward_and_reverse_actual_edges_verified': True,
        'selected_kernels': 'Previously constructed maximal conditional kernels on the full cell-state encoding',
        'roundtrip_preserves_native_endpoint_distribution': True,
        'source_state_reachable': True,
        'source_key_label': 0,
        'target_key_label': 2,
        'conditional_key_change_probability': '85/592',
        'both_boolean_messages_verified': True,
        'loop_and_identity_same_loss_budget': '37/64',
        'identity_loss_is_conservative_padding_not_actual_error': True,
        'no_four_cell_for_these_selected_paths': True,
        'no_diagram_edits_for_these_selected_paths': True,
        'different_choice_of_couplings_ruled_out': False,
        'cryptographic_reduction_impossibility_claimed': False,
        'public_key_hidden_advantage_claimed': False,
        'coupling_sampler_native_runtime_compiled': False,
        'novelty_and_necessity_assessment_owner': 'user',
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
    }, indent=2))

if __name__ == '__main__':
    main()
