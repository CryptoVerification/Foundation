import Foundation.Quantum.ClassicalComposition
import Foundation.Quantum.StateDistance
import Foundation.Quantum.RecordObservation
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

/-! An explicit finite-key ideal state with an abort flag, public transcript,
and a retained quantum adversary. This is our protocol-state interface for
subsequent error correction and privacy amplification, not a security theorem
for BB84. The actual real-to-ideal bound must be proved separately. -/
namespace Foundation.Quantum.QKD.IdealKey
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

abbrev Key (length : Nat) := Fin length → Fin 2

structure Output (T : Type) (length : Nat) where
  transcript : T
  accepted : Bool
  aliceKey : Option (Key length)
  bobKey : Option (Key length)
  deriving Fintype, DecidableEq

variable {T : Type} {length : Nat}

/-- The public view includes abort, so postselection is not implicit. -/
def publicView (r : Output T length) : T × Bool := (r.transcript,r.accepted)

/-- Overwrite both keys by one common fresh key on acceptance; clear them on abort. -/
def replace (x : Key length) (r : Output T length) : Output T length where
  transcript := r.transcript
  accepted := r.accepted
  aliceKey := if r.accepted then some x else none
  bobKey := if r.accepted then some x else none

@[simp] theorem publicView_replace (x : Key length) (r : Output T length) :
    publicView (replace x r) = publicView r := rfl

@[simp] theorem replace_replace (x y : Key length) (r : Output T length) :
    replace y (replace x r) = replace y r := rfl

@[simp] theorem replace_keys_agree (x : Key length) (r : Output T length) :
    (replace x r).aliceKey = (replace x r).bobKey := rfl

theorem replace_abort (x : Key length) (r : Output T length) (h : r.accepted = false) :
    (replace x r).aliceKey = none ∧ (replace x r).bobKey = none := by simp [replace,h]

theorem replace_accept (x : Key length) (r : Output T length) (h : r.accepted = true) :
    (replace x r).aliceKey = some x ∧ (replace x r).bobKey = some x := by simp [replace,h]

variable [Fintype T]

abbrev register (T : Type) [Fintype T] (length : Nat) :=
  Space.register (Fintype.card (Output T length))

def replaceLabel (x : Key length) : Fin (Fintype.card (Output T length)) →
    Fin (Fintype.card (Output T length)) :=
  fun r => Fintype.equivFin _ (replace x ((Fintype.equivFin _).symm r))

def publicLabel : Fin (Fintype.card (Output T length)) → Fin (Fintype.card (T × Bool)) :=
  fun r => Fintype.equivFin _ (publicView ((Fintype.equivFin _).symm r))

def publicChannel (e : Space) :
    Channel (.tensor (register T length) e) (.tensor (.register (Fintype.card (T × Bool))) e) :=
  classicalMap e publicLabel

/-- Actual density construction by fresh uniform randomness and verified
classical channels. The same quantum side information is retained. -/
def idealize {e : Space} (ρ : Density (.tensor (register T length) e)) :
    Density (.tensor (register T length) e) :=
  Density.mixture (Foundation.Probability.uniform (Key length))
    (fun x => (classicalMap e (replaceLabel x)).run ρ)

/-- Security compares the full joint state with this explicit ideal state. -/
def Secure {e : Space} (ρ : Density (.tensor (register T length) e)) (ε : ℝ) : Prop :=
  StateApprox ρ (idealize ρ) ε

private theorem weighted_constant {ι : Type*} [Fintype ι] {a : Space}
    (p : PMF ι) (M : Operator a) : ∑ x, ((p x).toReal : ℂ) • M = M := by
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, Density.probability_weights]
  simp

/-- Disclosing the transcript after replacing the keys is the same physical
 operation as disclosing it directly, including all quantum correlations. -/
theorem public_replace {e : Space} (ρ : Density (.tensor (register T length) e)) (x : Key length) :
    ((publicChannel e).run ((classicalMap e (replaceLabel x)).run ρ)).matrix =
      ((publicChannel e).run ρ).matrix := by
  change (classicalMap e publicLabel).toKraus.apply
    ((classicalMap e (replaceLabel x)).toKraus.apply ρ.matrix) =
      (classicalMap e publicLabel).toKraus.apply ρ.matrix
  rw [classicalMap_compose]
  have heq : publicLabel ∘ replaceLabel x = (publicLabel : Fin (Fintype.card (Output T length)) → _) := by
    funext r
    simp [publicLabel, replaceLabel]
  rw [heq]

/-- The whole public-and-adversary density is unchanged by idealization. -/
theorem public_idealize {e : Space} (ρ : Density (.tensor (register T length) e)) :
    ((publicChannel e).run (idealize ρ)).matrix = ((publicChannel e).run ρ).matrix := by
  rw [idealize, Density.mixture_channel]
  change (∑ x, (((Foundation.Probability.uniform (Key length)) x).toReal : ℂ) •
    ((publicChannel e).run ((classicalMap e (replaceLabel x)).run ρ)).matrix) = _
  simp_rw [public_replace]
  exact weighted_constant _ _

/-- Replacing already replaced keys overwrites them, and does not combine
 old key randomness with fresh key randomness. -/
theorem replace_after_replace {e : Space} (ρ : Density (.tensor (register T length) e))
    (x y : Key length) :
    ((classicalMap e (replaceLabel y)).run ((classicalMap e (replaceLabel x)).run ρ)).matrix =
      ((classicalMap e (replaceLabel y)).run ρ).matrix := by
  change (classicalMap e (replaceLabel y)).toKraus.apply
    ((classicalMap e (replaceLabel x)).toKraus.apply ρ.matrix) =
      (classicalMap e (replaceLabel y)).toKraus.apply ρ.matrix
  rw [classicalMap_compose]
  have heq : replaceLabel y ∘ replaceLabel x = (replaceLabel y : Fin (Fintype.card (Output T length)) → _) := by
    funext r
    simp [replaceLabel]
  rw [heq]

theorem replace_after_idealize {e : Space} (ρ : Density (.tensor (register T length) e)) (y : Key length) :
    ((classicalMap e (replaceLabel y)).run (idealize ρ)).matrix =
      ((classicalMap e (replaceLabel y)).run ρ).matrix := by
  rw [idealize, Density.mixture_channel]
  change (∑ x, (((Foundation.Probability.uniform (Key length)) x).toReal : ℂ) •
    ((classicalMap e (replaceLabel y)).run ((classicalMap e (replaceLabel x)).run ρ)).matrix) = _
  simp_rw [replace_after_replace]
  exact weighted_constant _ _

/-- The explicit idealization is idempotent on actual density operators. -/
theorem idealize_idempotent {e : Space} (ρ : Density (.tensor (register T length) e)) :
    (idealize (idealize ρ)).matrix = (idealize ρ).matrix := by
  change (∑ y, (((Foundation.Probability.uniform (Key length)) y).toReal : ℂ) •
    ((classicalMap e (replaceLabel y)).run (idealize ρ)).matrix) = _
  simp_rw [replace_after_idealize]
  rfl

/-- Fresh uniform key replacement cannot increase observational error. -/
theorem idealize_approx {e : Space} {ρ σ : Density (.tensor (register T length) e)} {ε : ℝ}
    (h : StateApprox ρ σ ε) : StateApprox (idealize ρ) (idealize σ) ε :=
  StateApprox.mixture_uniform_bound _ _ _ (fun x => StateApprox.postprocess (classicalMap e (replaceLabel x)) h)

/-- A perturbation of a secure state has a controlled security error.
 This composes proved bounds; it does not discharge the security premise. -/
theorem secure_perturbation {e : Space} {ρ σ : Density (.tensor (register T length) e)} {ε δ : ℝ}
    (h : Secure σ ε) (hρ : StateApprox ρ σ δ) : Secure ρ (δ+ε+δ) :=
  StateApprox.trans (StateApprox.trans hρ h) (StateApprox.symm (idealize_approx hρ))

/-- A fixed ideal state really satisfies the exact comparison. -/
theorem ideal_secure {e : Space} (ρ : Density (.tensor (register T length) e)) :
    Secure (idealize ρ) 0 := by
  intro E
  simp only [Effect.probability, idealize_idempotent, sub_self, abs_zero, le_refl]

/-- A classical event forbidden by every replacement has probability zero
 in the actual ideal density, for arbitrary quantum side information. -/
theorem idealize_event_zero {e : Space} (ρ : Density (.tensor (register T length) e))
    (P : Output T length → Prop) [DecidablePred P]
    (hP : ∀ x r, ¬ P (replace x r)) :
    (recordEvent e (fun r => P ((Fintype.equivFin _).symm r))).probability (idealize ρ) = 0 := by
  rw [idealize, Density.mixture_observation]
  apply Finset.sum_eq_zero
  intro x _
  have hx : (recordEvent e (fun r => P ((Fintype.equivFin _).symm r))).probability
      ((classicalMap e (replaceLabel x)).run ρ) = 0 := by
    rw [Effect.probability_run]
    unfold Effect.probability
    rw [classicalMap_recordEvent]
    have hz : (recordEvent e (fun r => P ((Fintype.equivFin _).symm (replaceLabel x r)))).matrix = 0 := by
      ext ⟨r,i⟩ ⟨s,j⟩
      simp [recordEvent, replaceLabel, hP]
    rw [hz]
    simp
  rw [hx, mul_zero]

/-- Alice and Bob never disagree in the ideal state, including abort. -/
theorem idealize_correct {e : Space} (ρ : Density (.tensor (register T length) e)) :
    (recordEvent e (fun r => let o : Output T length := (Fintype.equivFin _).symm r
      o.aliceKey ≠ o.bobKey)).probability (idealize ρ) = 0 := by
  classical
  exact idealize_event_zero ρ (fun o => o.aliceKey ≠ o.bobKey) (by intros; simp)

/-- Abort does not hide a surviving key in either private register. -/
theorem idealize_abort_empty {e : Space} (ρ : Density (.tensor (register T length) e)) :
    (recordEvent e (fun r => let o : Output T length := (Fintype.equivFin _).symm r
      o.accepted = false ∧ (o.aliceKey ≠ none ∨ o.bobKey ≠ none))).probability (idealize ρ) = 0 := by
  classical
  apply idealize_event_zero ρ (fun o => o.accepted = false ∧ (o.aliceKey ≠ none ∨ o.bobKey ≠ none))
  intro x r
  simp only [replace]
  cases r.accepted <;> simp

/-- Reconstruct an ideal private record using only public data and fresh randomness. -/
def reconstruct (x : Key length) (p : T × Bool) : Output T length :=
  ⟨p.1,p.2,if p.2 then some x else none,if p.2 then some x else none⟩

def reconstructLabel (x : Key length) : Fin (Fintype.card (T × Bool)) →
    Fin (Fintype.card (Output T length)) :=
  fun p => Fintype.equivFin _ (reconstruct x ((Fintype.equivFin _).symm p))

/-- Replacement factors through the public-and-adversary state. -/
theorem replace_from_public {e : Space} (ρ : Density (.tensor (register T length) e)) (x : Key length) :
    ((classicalMap e (reconstructLabel x)).run ((publicChannel e).run ρ)).matrix =
      ((classicalMap e (replaceLabel x)).run ρ).matrix := by
  change (classicalMap e (reconstructLabel x)).toKraus.apply
    ((classicalMap e publicLabel).toKraus.apply ρ.matrix) = _
  rw [classicalMap_compose]
  have heq : reconstructLabel x ∘ publicLabel = (replaceLabel x : Fin (Fintype.card (Output T length)) → _) := by
    funext r
    simp only [Function.comp_apply, reconstructLabel, publicLabel, Equiv.symm_apply_apply, replaceLabel]
    rfl
  rw [heq]
  rfl

/-- An explicit product random seed prepares the ideal state from the public
 quantum state alone; the real private key does not enter this preparation. -/
theorem idealize_from_public {e : Space} (ρ : Density (.tensor (register T length) e)) :
    (idealize ρ).matrix =
      (Density.mixture (Foundation.Probability.uniform (Key length))
        (fun x => (classicalMap e (reconstructLabel x)).run ((publicChannel e).run ρ))).matrix := by
  change (∑ x, _ • _) = ∑ x, _ • _
  apply Finset.sum_congr rfl
  intro x _
  rw [replace_from_public]

/-- Joint secrecy implies the operational correctness bound because the
 explicit ideal state assigns zero probability to unequal private keys. -/
theorem secure_correctness {e : Space} {ρ : Density (.tensor (register T length) e)} {ε : ℝ}
    (h : Secure ρ ε) :
    (recordEvent e (fun r => let o : Output T length := (Fintype.equivFin _).symm r
      o.aliceKey ≠ o.bobKey)).probability ρ ≤ ε := by
  classical
  have hh := h (recordEvent e (fun r => let o : Output T length := (Fintype.equivFin _).symm r
    o.aliceKey ≠ o.bobKey))
  rw [idealize_correct] at hh
  simpa only [sub_zero, abs_of_nonneg (Effect.probability_nonneg _ _)] using hh

end
end Foundation.Quantum.QKD.IdealKey
