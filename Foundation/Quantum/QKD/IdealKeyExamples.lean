import Foundation.Quantum.QKD.IdealKeyLogic

/-! A concrete accepted joint state with disagreeing keys is changed by the
idealization. It fails exact security; this rules out a vacuous definition.
The input is our validation example, not a BB84 execution claim. -/
namespace Foundation.Quantum.QKD.IdealKeyExamples
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

/-- Reading a predicate on a definite classical label has the expected probability. -/
theorem basis_record_probability {n : Nat} (e : Space) (P : Fin n → Prop) [DecidablePred P]
    (r : Fin n) (i : e.Basis) :
    (recordEvent e P).probability (basisDensity (.tensor (.register n) e) (r,i)) =
      if P r then 1 else 0 := by
  rw [recordEvent_probability]
  simp [basisDensity, Prod.mk.injEq, ite_and]
  simp_rw [apply_ite Complex.re]
  simp only [Complex.one_re, Complex.zero_re]
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hbr
    simp [hbr]
  · simp

def mismatch : IdealKey.Output Unit 1 := ⟨(),true,some (fun _ => 0),some (fun _ => 1)⟩

def mismatchState : Density (.tensor (IdealKey.register Unit 1) .bit) :=
  basisDensity _ (Fintype.equivFin _ mismatch,0)

def mismatchEffect : Effect (.tensor (IdealKey.register Unit 1) .bit) :=
  recordEvent .bit (fun r => let o : IdealKey.Output Unit 1 := (Fintype.equivFin _).symm r
    o.aliceKey ≠ o.bobKey)

theorem mismatch_probability : mismatchEffect.probability mismatchState = 1 := by
  unfold mismatchEffect mismatchState
  rw [basis_record_probability]
  simp only [Equiv.symm_apply_apply]
  have h : mismatch.aliceKey ≠ mismatch.bobKey := by
    intro heq
    have hh := congrArg (fun z : Option (IdealKey.Key 1) => z.map (fun k => k 0)) heq
    norm_num [mismatch] at hh
  simp [h]

theorem mismatch_ideal_probability : mismatchEffect.probability (IdealKey.idealize mismatchState) = 0 :=
  IdealKey.idealize_correct mismatchState

theorem idealization_changes_state : (IdealKey.idealize mismatchState).matrix ≠ mismatchState.matrix := by
  intro h
  have hh := mismatch_ideal_probability
  unfold Effect.probability at hh
  rw [h] at hh
  exact one_ne_zero (mismatch_probability.symm.trans hh)

/-- This valid normalized joint state cannot satisfy an error below one. -/
theorem mismatch_security_error {ε : ℝ} (h : IdealKey.Secure mismatchState ε) : 1 ≤ ε := by
  have hh := h mismatchEffect
  simpa only [mismatch_probability, mismatch_ideal_probability, sub_zero, abs_one] using hh

theorem mismatch_not_exact_secure : ¬ IdealKey.Secure mismatchState 0 := by
  intro h
  have hh := mismatch_security_error h
  norm_num at hh

/-- A closed proof is interpreted by an actual nontrivial idealization. -/
def fixedProof : Derivation IdealKeyLogic.presentation (Logic.Context.empty IdealKeyLogic.presentation)
    ⟨.ideal (.state 0),.ideal (.ideal (.state 0)),0⟩ :=
  .apply (T := IdealKeyLogic.presentation) (.fixed (.state 0)) (fun i => Fin.elim0 i)

theorem fixed_interpreted :
    (IdealKeyLogic.model (fun _ => mismatchState)).Carrier
      ⟨.ideal (.state 0),.ideal (.ideal (.state 0)),0⟩ :=
  IdealKeyLogic.sound (fun _ => mismatchState) fixedProof (fun i => Fin.elim0 i)

/-- Matching deterministic keys are correct but do not constitute a secret uniform key. -/
def chosen : IdealKey.Output Unit 1 := ⟨(),true,some (fun _ => 0),some (fun _ => 0)⟩
def chosenState : Density (.tensor (IdealKey.register Unit 1) .bit) :=
  basisDensity _ (Fintype.equivFin _ chosen,0)
def zeroKeyEffect : Effect (.tensor (IdealKey.register Unit 1) .bit) :=
  recordEvent .bit (fun r => let o : IdealKey.Output Unit 1 := (Fintype.equivFin _).symm r
    o.aliceKey = some (fun _ => 0))

theorem chosen_probability : zeroKeyEffect.probability chosenState = 1 := by
  unfold zeroKeyEffect chosenState
  rw [basis_record_probability]
  simp [chosen]

theorem chosen_ideal_probability : zeroKeyEffect.probability (IdealKey.idealize chosenState) = 1/2 := by
  rw [IdealKey.idealize, Density.mixture_observation]
  have hx (x : IdealKey.Key 1) : zeroKeyEffect.probability
      ((classicalMap .bit (IdealKey.replaceLabel x)).run chosenState) = if x = (fun _ => 0) then 1 else 0 := by
    rw [Effect.probability_run]
    unfold zeroKeyEffect Effect.probability
    rw [classicalMap_recordEvent]
    change (recordEvent .bit (fun r =>
      ((Fintype.equivFin (IdealKey.Output Unit 1)).symm (IdealKey.replaceLabel x r)).aliceKey = some (fun _ => 0))).probability chosenState = _
    unfold chosenState
    rw [basis_record_probability]
    simp [IdealKey.replaceLabel, IdealKey.replace, chosen]
  simp_rw [hx]
  norm_num [Foundation.Probability.uniform, PMF.uniformOfFintype_apply, IdealKey.Key,
    Fintype.card_fun, mul_ite]

/-- Even perfect key agreement does not discharge the secrecy requirement. -/
theorem chosen_security_error {ε : ℝ} (h : IdealKey.Secure chosenState ε) : 1/2 ≤ ε := by
  have hh := h zeroKeyEffect
  rw [chosen_probability, chosen_ideal_probability] at hh
  norm_num at hh ⊢
  exact hh

end
end Foundation.Quantum.QKD.IdealKeyExamples
