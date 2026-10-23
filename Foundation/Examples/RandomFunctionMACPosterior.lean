import Foundation.Crypto.Semantics.Oracle.PosteriorCoupling
import Foundation.Examples.ScheduleCertificate

/-! A concrete obstruction to identifying two chosen eager/lazy couplings.
This is the same three-query adaptive MAC attack, before final verification.
Both reconstructions have the correct full eager marginal. They do not share
the same future answer at the unqueried forgery message with probability one.
-/
namespace Foundation.Symmetric.RandomFunctionMACPosterior
open Foundation.Probability CryptoOracle CryptoOracle.RandomOracle
open CryptoOracle.RandomOracle.Posterior
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def Avoids {Input Tag Result : Type} (message : Input) : Program Input Tag Result → Prop
  | .done _ => True
  | .query request next => request ≠ message ∧ ∀ tag, Avoids message (next tag)
  | .coin next => ∀ bit, Avoids message (next bit)

theorem avoids_trace {Input Tag Result State : Type} (program : Program Input Tag Result)
    (message : Input) (avoids : Avoids message program) (world : Oracle Input Tag State)
    (state : State) (out : Outcome Input Tag Result State)
    (supported : out ∈ (program.run world state).support) :
    ∀ tag, (message, tag) ∉ out.trace := by
  induction program generalizing state out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at supported
      subst out
      simp
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at supported
      obtain ⟨bit, _, supported⟩ := supported
      exact ih bit (avoids bit) state out supported
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at supported
      obtain ⟨answer, _, supported⟩ := supported
      rw [PMF.mem_support_map_iff] at supported
      obtain ⟨tail, reachable, rfl⟩ := supported
      intro tag member
      rcases List.mem_cons.mp member with same | later
      · exact avoids.1 (congrArg Prod.fst same).symm
      · exact ih answer.2 (avoids.2 answer.2) answer.1 tail reachable tag later

theorem attack_avoids : Avoids 7 RandomFunctionMACSchedules.Examples.attack := by
  simp only [RandomFunctionMACSchedules.Examples.attack, Avoids]
  intro coin
  refine ⟨?_, fun tag => ⟨?_, fun second => ⟨?_, fun repeated => trivial⟩⟩⟩
  all_goals split <;> decide

abbrev SigningOutcome := Outcome (Fin 8) (Fin 256) (Fin 8 × Fin 256) (Table (Fin 8) (Fin 256))

noncomputable def signingHistory : PMF SigningOutcome :=
  RandomFunctionMACSchedules.Examples.attack.run oracle []

theorem signing_fresh (out : SigningOutcome) (supported : out ∈ signingHistory.support) :
    out.state.lookup 7 = none :=
  unqueried_fresh RandomFunctionMACSchedules.Examples.attack out supported 7
    (avoids_trace _ 7 attack_avoids oracle [] out supported)

noncomputable def keepFunction := shared signingHistory Outcome.state
noncomputable def restoreFunction := reconstructed signingHistory Outcome.state

theorem left_marginal :
    restoreFunction.map (fun triple => (triple.1, triple.2.1)) =
      keepFunction.map (fun triple => (triple.1, triple.2.1)) := by
  exact (reconstructed_left _ _).trans (shared_left _ _).symm

theorem right_marginal :
    restoreFunction.map (fun triple => (triple.1, triple.2.2)) =
      keepFunction.map (fun triple => (triple.1, triple.2.2)) := by
  exact (reconstructed_right _ _).trans (shared_right _ _).symm

/-- Even the complete cache and ordered adaptive transcript are retained.
Agreement of the future verification answers is nevertheless only 1/256. -/
theorem restored_verification_agreement :
    eventProb restoreFunction (fun triple => triple.2.1 7 = triple.2.2 7) = (256 : ℝ≥0∞)⁻¹ := by
  simpa only [restoreFunction, Fintype.card_fin, Nat.cast_ofNat] using
    reconstructed_agreement signingHistory Outcome.state (fun _ => 7) signing_fresh

theorem kept_verification_agreement :
    eventProb keepFunction (fun triple => triple.2.1 7 = triple.2.2 7) = 1 :=
  shared_agreement signingHistory Outcome.state (fun _ => 7)

theorem distinct_couplings : restoreFunction ≠ keepFunction := by
  apply reconstructed_ne_shared signingHistory Outcome.state (fun _ => 7) signing_fresh
  norm_num

theorem actual_eager_marginal :
    retained signingHistory Outcome.state =
      (uniform (Fin 8 → Fin 256)).bind (fun function =>
        (RandomFunctionMACSchedules.Examples.attack.run (eager function) []).map
          (fun out => (out, function))) := retained_eager _

/-- No procedure using only this complete signing history and independent
randomness can recover the original unqueried verification answer exactly. -/
theorem any_restoration_agreement (restore : SigningOutcome → PMF (Fin 8 → Fin 256)) :
    eventProb (reconstructWith signingHistory Outcome.state restore)
      (fun triple => triple.2.1 7 = triple.2.2 7) = (256 : ℝ≥0∞)⁻¹ := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    reconstructWith_agreement signingHistory Outcome.state restore (fun _ => 7) signing_fresh

theorem any_restoration_not_shared (restore : SigningOutcome → PMF (Fin 8 → Fin 256)) :
    reconstructWith signingHistory Outcome.state restore ≠ keepFunction := by
  apply reconstructWith_ne_shared signingHistory Outcome.state restore (fun _ => 7) signing_fresh
  norm_num

end Foundation.Symmetric.RandomFunctionMACPosterior
