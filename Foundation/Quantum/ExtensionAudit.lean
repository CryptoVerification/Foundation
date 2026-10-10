import Foundation.Examples.QuantumExtensions
import Foundation.Examples.QuantumContexts
import Foundation.Quantum.InfiniteLogic
import Foundation.Quantum.CoherentBridge
import Foundation.Quantum.ProbabilityBridge

/-! Kernel axiom dependencies of the probability, logic, and security extension. -/
#print axioms Foundation.Quantum.Kraus.linear
#print axioms Foundation.Quantum.Kraus.positive
#print axioms Foundation.Quantum.Kraus.trace_apply
#print axioms Foundation.Quantum.Kraus.completely_positive
#print axioms Foundation.Quantum.Kraus.seq_apply
#print axioms Foundation.Quantum.Channel.run
#print axioms Foundation.Quantum.Channel.amplify
#print axioms Foundation.Quantum.Channel.seq
#print axioms Foundation.Quantum.Effect.probability_nonneg
#print axioms Foundation.Quantum.Effect.probability_le_one
#print axioms Foundation.Quantum.Effect.probability_run
#print axioms Foundation.Quantum.Instrument.probability_sum
#print axioms Foundation.Quantum.Instrument.record
#print axioms Foundation.Quantum.discardRight_apply
#print axioms Foundation.Quantum.Approx.trans
#print axioms Foundation.Quantum.Approx.pre
#print axioms Foundation.Quantum.Approx.post
#print axioms Foundation.Quantum.Approx.seq
#print axioms Foundation.Quantum.approx_iff_adversaries
#print axioms Foundation.Quantum.Security.sound
#print axioms Foundation.Quantum.Security.interpretation_substitute
#print axioms Foundation.Quantum.Predicate.orthomodular
#print axioms Foundation.Quantum.Predicate.exists_pull
#print axioms Foundation.Quantum.Predicate.sasaki_adjunction
#print axioms Foundation.Quantum.Predicate.hook_formula
#print axioms Foundation.Quantum.Predicate.andThen_formula
#print axioms Foundation.Quantum.PredicateLogic.sound
#print axioms Foundation.Quantum.PredicateLogic.interpretation_substitute
#print axioms Foundation.Quantum.Bohr.tautological
#print axioms Foundation.Quantum.Bohr.Persistent.implication_adjunction
#print axioms Foundation.Quantum.Bohr.sound
#print axioms Foundation.Quantum.Bohr.interpretation_substitute
#print axioms Foundation.Quantum.Infinite.double_orthogonal
#print axioms Foundation.Quantum.Infinite.kernel_adjoint
#print axioms Foundation.Quantum.Infinite.sequence_space_approximation
#print axioms Foundation.Quantum.InfiniteLogic.sound
#print axioms Foundation.Quantum.InfiniteLogic.interpretation_substitute
#print axioms Foundation.Quantum.InfiniteLogic.sequence_transport
#print axioms Foundation.Quantum.coherent_auxiliary_sound
#print axioms Foundation.Quantum.approximate_of_coherent_eq
#print axioms Foundation.Quantum.OneTimePad.decrypt_encrypt
#print axioms Foundation.Quantum.OneTimePad.average_auxiliary
#print axioms Foundation.Quantum.OneTimePad.perfect_privacy
#print axioms Foundation.Quantum.Instrument.classicalOutcome_event
#print axioms Foundation.Quantum.Adversary.experiment_acceptance
#print axioms Foundation.Quantum.oneTimePad_existing_probability
#print axioms Foundation.Quantum.ExtensionExamples.measured_probability
#print axioms Foundation.Quantum.ExtensionExamples.otp_interpreted
#print axioms Foundation.Quantum.ExtensionExamples.noncommuting_measurements
#print axioms Foundation.Quantum.ContextExamples.excluded_middle_not_derivable
#print axioms Foundation.Quantum.ExtensionExamples.mix_transport_interpreted
