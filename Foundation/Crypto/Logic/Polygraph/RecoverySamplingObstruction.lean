import Foundation.Crypto.Semantics.Machine.FiniteFairExecution
import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoveryError

/-! The selected five-state conditional recovery kernels cannot be sampled
exactly by any fixed-budget fair-bit native program from a fixed initial state.
This concerns conditional kernels, not merely their dyadic endpoint marginals.
Approximation and almost-sure termination with no uniform budget remain open. -/
namespace CryptoLogic.Polygraph.Experiment.RecoverySamplingObstruction
open Foundation.Probability FiniteFairSampling
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section

theorem forward_row_not_realizable (n : Nat) : ¬Realizable n (RecoveryError.attainingForward 2) := by
  apply no_reciprocal_odd_factor n 21 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ (fun key => key = 0)
  rw [FiniteRecoveryError.singleton, RecoveryError.forward_matrix]
  rfl

theorem reverse_row_not_realizable (n : Nat) : ¬Realizable n (RecoveryError.preservingReverse 1) := by
  apply no_reciprocal_odd_factor n 44 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ (fun key => key = 2)
  rw [FiniteRecoveryError.singleton, RecoveryError.reverse_matrix]
  rfl

theorem no_native_forward (program : Machine.Program) (state : Machine.Configuration) (steps : Nat)
    (observe : Machine.Configuration → Fin 5) :
    (Machine.evalConfigWithin program state steps).map observe ≠ RecoveryError.attainingForward 2 := by
  intro same
  exact forward_row_not_realizable steps (same ▸ Machine.FiniteFairExecution.observed_realizable program state steps observe)

theorem no_native_reverse (program : Machine.Program) (state : Machine.Configuration) (steps : Nat)
    (observe : Machine.Configuration → Fin 5) :
    (Machine.evalConfigWithin program state steps).map observe ≠ RecoveryError.preservingReverse 1 := by
  intro same
  exact reverse_row_not_realizable steps (same ▸ Machine.FiniteFairExecution.observed_realizable program state steps observe)

theorem forward_approximation_lower (n : Nat) (law : PMF (Fin 5)) (realizable : Realizable n law) :
    1 / (21 * (2 ^ n : Nat) : ℝ) ≤ finiteVariation law (RecoveryError.attainingForward 2) := by
  have notDivides : ¬21 ∣ 2 ^ n := by
    intro h
    have impossible := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow ((show 3 ∣ 21 by norm_num).trans h)
    norm_num at impossible
  have lower := reciprocal_error_lower n 21 (by norm_num) notDivides law realizable (fun key => key = 0)
  have target : (eventProb (RecoveryError.attainingForward 2) (fun key => key = 0)).toReal = 1 / 21 := by
    rw [FiniteRecoveryError.singleton, RecoveryError.forward_matrix]
    rfl
  have upper := probabilistic_event_real_bound law (RecoveryError.attainingForward 2)
    PMF.pure (fun key => key = 0)
  simp only [PMF.bind_pure, target] at upper
  exact lower.trans upper

theorem native_forward_approximation_lower (program : Machine.Program) (state : Machine.Configuration) (steps : Nat)
    (observe : Machine.Configuration → Fin 5) :
    1 / (21 * (2 ^ steps : Nat) : ℝ) ≤
      finiteVariation ((Machine.evalConfigWithin program state steps).map observe) (RecoveryError.attainingForward 2) :=
  forward_approximation_lower steps _ (Machine.FiniteFairExecution.observed_realizable program state steps observe)

end
end CryptoLogic.Polygraph.Experiment.RecoverySamplingObstruction
