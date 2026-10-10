import Foundation.Examples.QuantumLogic

/-! Explicit axiom dependency audit for the selected foundation. The output
must contain no sorryAx or project-defined axiom. Standard Lean foundations
(propext, Classical.choice, Quot.sound) are permitted and documented. -/
#print axioms Foundation.Quantum.matrixMonoidal
#print axioms Foundation.Quantum.matrixPairing
#print axioms Foundation.Quantum.matrixRigid
#print axioms Foundation.Quantum.matrixSymmetric
#print axioms Foundation.Quantum.Op.snake_left
#print axioms Foundation.Quantum.Op.snake_right
#print axioms Foundation.Quantum.standardClassical
#print axioms Foundation.Quantum.dagger_compact
#print axioms Foundation.Quantum.Op.mix_dagger_epi
#print axioms Foundation.Quantum.Law.valid
#print axioms Foundation.Quantum.Proof.qkd
#print axioms Foundation.Quantum.sound
#print axioms Foundation.Quantum.interpretation_substitute
#print axioms Foundation.Quantum.qkd_correct
#print axioms Foundation.Quantum.qkdMix
#print axioms Foundation.Quantum.Derived.expansion
#print axioms Foundation.Quantum.Derived.interpretation_expansion
#print axioms Foundation.Quantum.Op.linear_dagger
#print axioms Foundation.Quantum.qkd_hilbert
#print axioms Foundation.Quantum.Examples.qkd_mix
#print axioms Foundation.Quantum.Examples.measured_mix
#print axioms Foundation.Quantum.Examples.classical_copy_not_clone
#print axioms Foundation.Quantum.Examples.no_zero_identity
#print axioms Foundation.Quantum.Examples.distinct_proofs
