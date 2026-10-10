import Foundation.Quantum.QKD.CommonKeyIdealization
import Foundation.Quantum.QKD.IdealKey

/-! Join an accepted subnormalized two-key branch with its unchanged abort
branch. The comparison is the existing IdealKey.idealize of the actual
normalized output, not an independently postulated ideal state. -/
namespace Foundation.Quantum.QKD.AcceptedAbort
noncomputable section
open scoped ComplexOrder
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
variable {T : Type} [Fintype T] [DecidableEq T] {length : Nat} {e : Space}
abbrev K (length : Nat) := IdealKey.Key length
abbrev AcceptedLabel (T : Type) (length : Nat) := ((K length × K length) × T)

def acceptLabel (p : AcceptedLabel T length) : IdealKey.Output T length :=
  ⟨p.2,true,some p.1.1,some p.1.2⟩

def abortLabel (t : T) : IdealKey.Output T length := ⟨t,false,none,none⟩

def acceptChannel (e : Space) :
    Channel (Guessing.publicSpace (AcceptedLabel T length) e)
      (.tensor (IdealKey.register T length) e) :=
  classicalMap e (fun r => Fintype.equivFin _ (acceptLabel ((Fintype.equivFin _).symm r)))

/-- Both branches retain their original weight and quantum auxiliary system. -/
def state (ρ : State (AcceptedLabel T length) e) (σ : State T e)
    (hmass : mass ρ + mass σ = 1) : Density (.tensor (IdealKey.register T length) e) where
  matrix := joint (relabel ρ acceptLabel) + joint (relabel σ (abortLabel (length := length)))
  positive := (joint_positive _).add (joint_positive _)
  normalized := by
    rw [Matrix.trace_add, joint_trace_complex, joint_trace_complex, mass_relabel, mass_relabel,
      ← Complex.ofReal_add, hmass]
    rfl

/-- Replacing keys preserves every abort block exactly. -/
theorem replace_abort (σ : State T e) (x : K length) :
    (classicalMap e (IdealKey.replaceLabel x)).toKraus.apply (joint (relabel σ (abortLabel (length := length)))) =
      joint (relabel σ (abortLabel (length := length))) := by
  unfold IdealKey.replaceLabel
  rw [← relabel_physical (relabel σ (abortLabel (length := length))) (IdealKey.replace x), relabel_comp]
  rfl

/-- Replacing keys in the accepted embedding is the accepted embedding of
replacement. Equality concerns operations, not their Kraus representations. -/
theorem replace_accept (ρ : State (AcceptedLabel T length) e) (x : K length) :
    (classicalMap e (IdealKey.replaceLabel x)).toKraus.apply (joint (relabel ρ acceptLabel)) =
      (acceptChannel (T := T) (length := length) e).toKraus.apply
        (joint (relabel ρ (CommonKey.replaceKeys x))) := by
  unfold IdealKey.replaceLabel
  rw [← relabel_physical (relabel ρ acceptLabel) (IdealKey.replace x)]
  change joint (relabel (relabel ρ acceptLabel) (IdealKey.replace x)) =
    (classicalMap e _).toKraus.apply _
  rw [← relabel_physical (relabel ρ (CommonKey.replaceKeys x)) acceptLabel, relabel_comp, relabel_comp]
  rfl

/-- Fresh uniform replacement agrees with the accepted common-key ideal. -/
theorem accepted_ideal (ρ : State (AcceptedLabel T length) e) :
    (∑ x : K length, ((1/(Fintype.card (K length):ℝ):ℝ):ℂ) •
      (classicalMap e (IdealKey.replaceLabel x)).toKraus.apply (joint (relabel ρ acceptLabel))) =
      joint (relabel (CommonKey.ideal ρ) acceptLabel) := by
  simp_rw [replace_accept]
  let C := acceptChannel (T := T) (length := length) e
  have h := congrArg C.toKraus.linear (CommonKey.ideal_uniform_replacement ρ)
  simp only [map_sum, map_smul] at h
  change (acceptChannel (T := T) (length := length) e).toKraus.apply (joint (CommonKey.ideal ρ)) = _ at h
  unfold acceptChannel at h
  rw [← relabel_physical (CommonKey.ideal ρ) acceptLabel] at h
  exact h.symm

/-- The existing full-output idealization changes just the accepted branch.
The same abort transcript and quantum blocks occur on both sides. -/
theorem idealize_state (ρ : State (AcceptedLabel T length) e) (σ : State T e)
    (hmass : mass ρ + mass σ = 1) :
    (IdealKey.idealize (state ρ σ hmass)).matrix =
      joint (relabel (CommonKey.ideal ρ) acceptLabel) + joint (relabel σ (abortLabel (length := length))) := by
  change (∑ x : K length, (((Foundation.Probability.uniform (K length)) x).toReal:ℂ) •
    (classicalMap e (IdealKey.replaceLabel x)).toKraus.linear
      (joint (relabel ρ acceptLabel) + joint (relabel σ (abortLabel (length := length))))) = _
  simp only [map_add, smul_add, Finset.sum_add_distrib]
  have ha (x : K length) := replace_abort σ x
  change (∑ x : K length, (((Foundation.Probability.uniform (K length)) x).toReal:ℂ) •
    (classicalMap e (IdealKey.replaceLabel x)).toKraus.apply (joint (relabel ρ acceptLabel))) +
      (∑ x : K length, (((Foundation.Probability.uniform (K length)) x).toReal:ℂ) •
        (classicalMap e (IdealKey.replaceLabel x)).toKraus.apply (joint (relabel σ (abortLabel (length := length))))) = _
  simp_rw [ha]
  have hw (x : K length) : (((Foundation.Probability.uniform (K length)) x).toReal:ℂ) =
      ((1/(Fintype.card (K length):ℝ):ℝ):ℂ) := by
    simp [Foundation.Probability.uniform, PMF.uniformOfFintype_apply]
  have habort : (∑ x : K length, (((Foundation.Probability.uniform (K length)) x).toReal:ℂ) •
      joint (relabel σ (abortLabel (length := length)))) = joint (relabel σ (abortLabel (length := length))) := by
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, Density.probability_weights, Complex.ofReal_one, one_smul]
  rw [habort]
  simp_rw [hw]
  rw [accepted_ideal]

/-- The weighted accepted disagreement is exactly the actual physical
mismatch probability in the full output; abort contributes zero. -/
theorem correctness_probability (ρ : State (AcceptedLabel T length) e) (σ : State T e)
    (hmass : mass ρ + mass σ = 1) :
    (recordEvent e (fun r => let o : IdealKey.Output T length := (Fintype.equivFin _).symm r
      o.aliceKey ≠ o.bobKey)).probability (state ρ σ hmass) = CommonKey.correctnessError ρ := by
  unfold Effect.probability
  change ((recordEvent e _).matrix * (joint (relabel ρ acceptLabel) +
    joint (relabel σ (abortLabel (length := length))))).trace.re = _
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rw [relabel_event_observation (ρ := ρ) (f := acceptLabel) (P := fun o => o.aliceKey ≠ o.bobKey),
    relabel_event_observation (ρ := σ) (f := abortLabel) (P := fun o => o.aliceKey ≠ o.bobKey)]
  simp only [acceptLabel, abortLabel, ne_eq, Option.some.injEq, not_true_eq_false, ite_false,
    Finset.sum_const_zero, add_zero, CommonKey.correctnessError, ite_not]

/-- An accepted-branch comparison implies the full existing security judgment. -/
theorem secure_of_common (ρ : State (AcceptedLabel T length) e) (σ : State T e)
    (hmass : mass ρ + mass σ = 1) (η : ℝ)
    (hcommon : OperatorApprox (joint ρ) (joint (CommonKey.ideal ρ)) η) :
    IdealKey.Secure (state ρ σ hmass) η := by
  have h := OperatorApprox.postprocess (acceptChannel (T := T) (length := length) e)
    hcommon
  change OperatorApprox ((classicalMap e _).toKraus.apply (joint ρ))
    ((classicalMap e _).toKraus.apply (joint (CommonKey.ideal ρ))) η at h
  rw [← relabel_physical ρ acceptLabel, ← relabel_physical (CommonKey.ideal ρ) acceptLabel] at h
  intro E
  change |(E.matrix*(state ρ σ hmass).matrix).trace.re -
    (E.matrix*(IdealKey.idealize (state ρ σ hmass)).matrix).trace.re| ≤ η
  rw [idealize_state]
  change |(E.matrix*(joint (relabel ρ acceptLabel) + joint (relabel σ (abortLabel (length := length))))).trace.re - _| ≤ _
  simpa only [Matrix.mul_add, Matrix.trace_add, Complex.add_re, add_sub_add_right_eq_sub] using h E

/-- Correctness and Alice-key secrecy on the unnormalized accepted branch
imply security of the actual full density, including abort. -/
theorem secure (ρ : State (AcceptedLabel T length) e) (σ : State T e)
    (hmass : mass ρ + mass σ = 1) (δ ε : ℝ)
    (hc : CommonKey.correctnessError ρ ≤ δ)
    (hs : OperatorApprox (joint (CommonKey.aliceView ρ))
      (joint (CommonKey.uniformize (CommonKey.aliceView ρ))) ε) :
    IdealKey.Secure (state ρ σ hmass) (δ+ε) :=
  secure_of_common ρ σ hmass (δ+ε) (CommonKey.compose ρ δ ε hc hs)

end
end Foundation.Quantum.QKD.AcceptedAbort
