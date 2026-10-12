import Foundation.Quantum.QKD.BB84Completion

/-! Minimal paper entrypoint: standard distance, concrete finite-key security,
and physical honest-run availability. Reproduction checks these dependencies. -/
#print axioms Foundation.Quantum.HermitianTrace.sqrt_gram_eq_absolute
#print axioms Foundation.Quantum.Density.traceDistance_eq_half_traceNorm
#print axioms Foundation.Quantum.Density.exists_effect_attaining_traceDistance
#print axioms Foundation.Quantum.Density.stateApprox_iff_traceDistance_le
#print axioms Foundation.Quantum.QKD.traceDistance_orthogonal_qubits
#print axioms Foundation.Quantum.QKD.IdealKey.secure_iff_traceDistance
#print axioms Foundation.Quantum.QKD.UsefulBB84.secure
#print axioms Foundation.Quantum.QKD.UsefulBB84.secure_traceDistance
#print axioms Foundation.Quantum.QKD.UsefulBB84.secure_half_traceNorm
#print axioms Foundation.Quantum.QKD.HonestBB84.supported_matched
#print axioms Foundation.Quantum.QKD.HonestBB84.outcome_eq_records
#print axioms Foundation.Quantum.QKD.HonestBB84.outcome_eq_errorFreeRecords
#print axioms Foundation.Quantum.QKD.UsefulBB84.honest_raw_success
#print axioms Foundation.Quantum.QKD.UsefulBB84.honest_success
#print axioms Foundation.Quantum.QKD.UsefulBB84.output_positive
