import Foundation.Crypto.Logic.Polygraph.OracleRefreshCells
import Foundation.Crypto.Logic.Polygraph.OracleRefreshGames
import Foundation.Crypto.Meta.Polygraph.OracleRefreshCertificate
import Foundation.Examples.RandomFunctionMACPosterior

/-! Selected-kernel diagrams on the same MAC's actual signing history.
Message 6 and message 7 are both unqueried. Swapping their refreshes preserves
the joint law with the original secret; replacing refresh 6 with refresh 7
does not, despite equal game marginals and equal numbers of draws.
-/
namespace Foundation.Symmetric.RandomFunctionMACRefresh
open Foundation.Probability CryptoOracle CryptoOracle.RandomOracle
open CryptoOracle.RandomOracle.Posterior CryptoOracle.ProofEdits
open RandomFunctionMACPosterior
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev State := SigningOutcome × (Fin 8 → Fin 256)
def coordinate (index : Fin 8) (_past : SigningOutcome) : Fin 8 := index

theorem attack_avoids_six : Avoids 6 RandomFunctionMACSchedules.Examples.attack := by
  simp only [RandomFunctionMACSchedules.Examples.attack, Avoids]
  intro coin
  refine ⟨?_, fun tag => ⟨?_, fun second => ⟨?_, fun repeated => trivial⟩⟩⟩
  all_goals split <;> decide

theorem six_fresh (out : SigningOutcome) (supported : out ∈ signingHistory.support) :
    out.state.lookup 6 = none :=
  unqueried_fresh RandomFunctionMACSchedules.Examples.attack out supported 6
    (avoids_trace _ 6 attack_avoids_six oracle [] out supported)

def swap : Refresh.Cell ([7, 6] : List (Fin 8)) [6, 7] := .exchange 7 6 []

theorem swap_kernel (state : State) :
    Refresh.run coordinate [7, 6] state = Refresh.run coordinate [6, 7] state := swap.sound coordinate state

theorem swap_joint :
    Refresh.joint signingHistory Outcome.state coordinate [7, 6] =
      Refresh.joint signingHistory Outcome.state coordinate [6, 7] := swap.joint_eq _ _ _

/-- The last verification is actual postprocessing of the transformed
function, not an observer that forgets it. -/
noncomputable def verify (state : State) : PMF Bool :=
  PMF.pure (decide (state.2 7 = state.1.result.2))

theorem swap_verification (state : State) :
    (Refresh.run coordinate [7, 6] state).bind verify =
      (Refresh.run coordinate [6, 7] state).bind verify := swap.continuation coordinate verify state

def coalesce : Refresh.Improvement ([7, 6, 7] : List (Fin 8)) [6, 7] :=
  .trans (.exchange (.exchange 7 6 [7])) (.cons 6 (.duplicate 7 []))

theorem coalesce_kernel (state : State) :
    Refresh.run coordinate [7, 6, 7] state = Refresh.run coordinate [6, 7] state :=
  coalesce.sound coordinate state

theorem coalesce_draws : ([6, 7] : List (Fin 8)).length < [7, 6, 7].length := by decide

noncomputable def replaceSix := Refresh.joint signingHistory Outcome.state coordinate [7, 6]
noncomputable def keepSix := Refresh.joint signingHistory Outcome.state coordinate [7, 7]

theorem replaced_six_agreement :
    eventProb replaceSix (fun pair => pair.1.2 6 = pair.2.2 6) = (256 : ℝ≥0∞)⁻¹ := by
  simpa only [replaceSix, coordinate, Fintype.card_fin, Nat.cast_ofNat, List.cons_append, List.nil_append] using
    Refresh.joint_last_agreement signingHistory Outcome.state coordinate [7] 6

theorem kept_six_agreement :
    eventProb keepSix (fun pair => pair.1.2 6 = pair.2.2 6) = 1 := by
  apply Refresh.joint_untouched_agreement signingHistory Outcome.state coordinate [7, 7] (fun _ => 6)
  intro past index member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst index
  change (7 : Fin 8) ≠ 6
  decide

theorem distinct_selected_kernels : replaceSix ≠ keepSix := by
  intro same
  have agreement := replaced_six_agreement
  rw [same, kept_six_agreement] at agreement
  have different : (256 : ℝ≥0∞)⁻¹ ≠ 1 := by norm_num
  exact different agreement.symm

theorem no_cell_between_replacement_and_retention :
    ¬Nonempty (Refresh.Cell ([7, 6] : List (Fin 8)) [7, 7]) := by
  rintro ⟨cell⟩
  have impossible : (6 : Fin 8) ∈ ([7, 7] : List (Fin 8)) := cell.perm.mem_iff.mp (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at impossible
  exact (by decide : (6 : Fin 8) ≠ 7) impossible

theorem same_original_marginal : replaceSix.map Prod.fst = keepSix.map Prod.fst := by
  exact (Refresh.joint_left _ _ _ _).trans (Refresh.joint_left _ _ _ _).symm

theorem same_transformed_marginal : replaceSix.map Prod.snd = keepSix.map Prod.snd := by
  have first := Refresh.joint_right signingHistory Outcome.state coordinate [7, 6] (by
    intro index member past supported
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact signing_fresh past supported
    · exact six_fresh past supported)
  have second := Refresh.joint_right signingHistory Outcome.state coordinate [7, 7] (by
    intro index member past supported
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst index
    exact signing_fresh past supported)
  exact first.trans second.symm

theorem certificate_accepts :
    Refresh.Certificate.accepts ([7, 6] : List (Fin 8)) [6, 7] [0] = true := by decide

theorem certificate_verification (state : State) :
    (Refresh.run coordinate [7, 6] state).bind verify =
      (Refresh.run coordinate [6, 7] state).bind verify := by
  obtain ⟨cell⟩ := Refresh.Certificate.accepts_sound _ _ _ certificate_accepts
  exact cell.continuation coordinate verify state

theorem rejects_any_certificate (positions : List Nat) :
    Refresh.Certificate.accepts ([7, 6] : List (Fin 8)) [7, 7] positions = false := by
  apply Refresh.Certificate.rejects_nonpermutation
  intro permutation
  have impossible : (6 : Fin 8) ∈ ([7, 7] : List (Fin 8)) := permutation.mem_iff.mp (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at impossible
  exact (by decide : (6 : Fin 8) ≠ 7) impossible

theorem word_fresh (word : List (Fin 8)) (valid : ∀ index ∈ word, index = 6 ∨ index = 7) :
    ∀ index ∈ word, ∀ past ∈ signingHistory.support, past.state.lookup (coordinate index past) = none := by
  intro index member past supported
  rcases valid index member with rfl | rfl
  · exact six_fresh past supported
  · exact signing_fresh past supported

noncomputable def asGameCell := Refresh.Games.interpret_cell signingHistory Outcome.state
  (fun out => out.result.2.val % 2 = 0) coordinate swap
  (word_fresh [7, 6] (by intro index member; simpa [or_comm] using member))
  (word_fresh [6, 7] (by intro index member; simpa using member))

noncomputable def verificationGame (word : List (Fin 8)) : PMF Bool :=
  ((retained signingHistory Outcome.state).bind (Refresh.run coordinate word)).bind verify

/-- Fresh-coordinate edits preserve the actual last verification experiment.
The 1/256 equality follows from the local fresh-coordinate law, not from an
already proved bound for this attack or a claimed identity of secret keys. -/
theorem verification_probability (word : List (Fin 8))
    (valid : ∀ index ∈ word, index = 6 ∨ index = 7) :
    eventProb (verificationGame word) (· = true) = (256 : ℝ≥0∞)⁻¹ := by
  unfold verificationGame
  rw [Refresh.run_preserve signingHistory Outcome.state coordinate word (word_fresh word valid)]
  change eventProb ((retained signingHistory Outcome.state).map
    (fun state => decide (state.2 7 = state.1.result.2))) (· = true) = _
  rw [eventProb_map]
  unfold retained
  apply event_bind_constant
  intro past supported
  rw [eventProb_map]
  simp only [decide_eq_true_eq]
  have value := congrArg (fun law => eventProb law (· = past.result.2))
    (reserve_fresh past.state 7 (signing_fresh past supported))
  simpa only [eventProb_map, Fintype.card_fin, Nat.cast_ofNat] using value.trans (uniform_guess _)

end Foundation.Symmetric.RandomFunctionMACRefresh
