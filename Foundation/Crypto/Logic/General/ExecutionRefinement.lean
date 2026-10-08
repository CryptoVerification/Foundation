import Foundation.Crypto.Logic.General.Execution

/-! Add proved resource conditions to existing represented attack classes.
Code, resources, realization and cryptographic losses are retained. Original
admissibility is preserved, even for objects whose realization is broader. -/
namespace CryptoLogic.General
universe u v
set_option backward.isDefEq.respectTransparency false

namespace SecurityObject
variable {K : CodeSystem} {m : K.Machine} (X : SecurityObject.{u, v} K m)

abbrev Certificate := InstanceFamily X.goal → K.Code m → X.execution.Resources → Prop

def refine (Q : X.Certificate) : SecurityObject.{u, v} K m where
  goal := X.goal
  execution := {
    Resources := X.execution.Resources
    ExecutesWithin := fun F code r => X.execution.ExecutesWithin F code r ∧ Q F code r
    Realizes := X.execution.Realizes }
  adversaries := { admissible := fun F A => X.adversaries.admissible F A ∧
    ∃ code r, X.execution.ExecutesWithin F code r ∧ Q F code r ∧ X.execution.Realizes F A code r }
  represented := by
    intro F A h
    obtain ⟨code, r, hExec, hQ, hReal⟩ := h.2
    exact ⟨code, r, ⟨hExec, hQ⟩, hReal⟩

variable {X}

def forget (Q : X.Certificate) (F A) (W : (X.refine Q).Witness F A) : X.Witness F A :=
  ⟨W.code, W.resources, W.executes.1, W.realizes, W.admissible.1⟩

def attach (Q : X.Certificate) (F A) (W : X.Witness F A) (hQ : Q F W.code W.resources) :
    (X.refine Q).Witness F A :=
  ⟨W.code, W.resources, ⟨W.executes, hQ⟩, W.realizes,
    ⟨W.admissible, W.code, W.resources, W.executes, hQ, W.realizes⟩⟩

@[simp] theorem forget_attach (Q : X.Certificate) (F A) (W : X.Witness F A)
    (hQ : Q F W.code W.resources) : forget Q F A (attach Q F A W hQ) = W := by
  cases W
  rfl

@[simp] theorem attach_forget (Q : X.Certificate) (F A) (W : (X.refine Q).Witness F A) :
    attach Q F A (forget Q F A W) W.executes.2 = W := by
  cases W
  rfl

theorem refined_admissible_iff (Q : X.Certificate) (F A) :
    (X.refine Q).adversaries.admissible F A ↔ ∃ W : X.Witness F A, Q F W.code W.resources := by
  constructor
  · intro h
    obtain ⟨code, r, hExec, hQ, hReal⟩ := h.2
    exact ⟨⟨code, r, hExec, hReal, h.1⟩, hQ⟩
  · rintro ⟨W, hQ⟩
    exact (attach Q F A W hQ).admissible

theorem refined_secure_of_secure (Q : X.Certificate) (F) (h : X.Secure F) : (X.refine Q).Secure F := by
  intro A hA
  exact h A hA.1

/-- A stronger certificate gives a smaller represented adversary class. -/
theorem refined_secure_mono (Q R : X.Certificate)
    (hQR : ∀ F code r, X.execution.ExecutesWithin F code r → Q F code r → R F code r)
    (F) (h : (X.refine R).Secure F) : (X.refine Q).Secure F := by
  intro A hA
  obtain ⟨W, hQ⟩ := (refined_admissible_iff Q F A).mp hA
  exact h A (attach R F A W (hQR F W.code W.resources W.executes hQ)).admissible

/-- Adding two conditions at once or successively defines the same class. -/
theorem refine_conjunction_admissible (Q R : X.Certificate) (F A) :
    ((X.refine Q).refine R).adversaries.admissible F A ↔
      (X.refine (fun F code r => Q F code r ∧ R F code r)).adversaries.admissible F A := by
  constructor
  · rintro ⟨hQ, code, r, ⟨hExec, hCodeQ⟩, hR, hReal⟩
    exact ⟨hQ.1, code, r, hExec, ⟨hCodeQ, hR⟩, hReal⟩
  · rintro ⟨hA, code, r, hExec, ⟨hQ, hR⟩, hReal⟩
    exact ⟨⟨hA, code, r, hExec, hQ, hReal⟩, code, r, ⟨hExec, hQ⟩, hR, hReal⟩

end SecurityObject

namespace CertifiedTransform
variable {K : CodeSystem} {m n : K.Machine}
    {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n}

/-- Lift precisely the existing emitted code when the added condition is
proved for its existing witness map. No new compiler primitive is introduced. -/
def refine (T : CertifiedTransform X Y) (Q : X.Certificate) (R : Y.Certificate)
    (hResource : ∀ F A (W : X.Witness F A), Q F W.code W.resources →
      R (T.transform.mapFamily F) (T.mapWitness F A W).code (T.mapWitness F A W).resources) :
    CertifiedTransform (X.refine Q) (Y.refine R) where
  transform := T.transform
  compiler := T.compiler
  mapWitness := fun F A W =>
    SecurityObject.attach R _ _ (T.mapWitness F A (SecurityObject.forget Q F A W))
      (hResource F A (SecurityObject.forget Q F A W) W.executes.2)
  code_eq := by intro F A W; exact T.code_eq F A (SecurityObject.forget Q F A W)

end CertifiedTransform

namespace CertifiedReduction
variable {K : CodeSystem} {m n : K.Machine}
    {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n}

def refine (T : CertifiedReduction X Y) (Q : X.Certificate) (R : Y.Certificate)
    (hResource : ∀ F A (W : X.Witness F A), Q F W.code W.resources →
      R (T.reduction.mapFamily F) (T.mapWitness F A W).code (T.mapWitness F A W).resources) :
    CertifiedReduction (X.refine Q) (Y.refine R) where
  reduction := T.reduction
  compiler := T.compiler
  mapWitness := fun F A W =>
    SecurityObject.attach R _ _ (T.mapWitness F A (SecurityObject.forget Q F A W))
      (hResource F A (SecurityObject.forget Q F A W) W.executes.2)
  code_eq := by intro F A W; exact T.code_eq F A (SecurityObject.forget Q F A W)
  negligible := T.negligible

end CertifiedReduction

namespace CertifiedBinaryReduction
variable {K : CodeSystem} {m n k : K.Machine}
    {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n} {Z : SecurityObject.{u, v} K k}

/-- Both branches carry their own added resource condition while the
original two-assumption advantage inequality and losses are preserved. -/
def refine (T : CertifiedBinaryReduction X Y Z)
    (Q : X.Certificate) (R : Y.Certificate) (S : Z.Certificate)
    (hLeft : ∀ F A (W : X.Witness F A), Q F W.code W.resources →
      R (T.left.transform.mapFamily F) (T.left.mapWitness F A W).code (T.left.mapWitness F A W).resources)
    (hRight : ∀ F A (W : X.Witness F A), Q F W.code W.resources →
      S (T.right.transform.mapFamily F) (T.right.mapWitness F A W).code (T.right.mapWitness F A W).resources) :
    CertifiedBinaryReduction (X.refine Q) (Y.refine R) (Z.refine S) where
  left := T.left.refine Q R hLeft
  right := T.right.refine Q S hRight
  leftLoss := T.leftLoss
  rightLoss := T.rightLoss
  leftNegligible := T.leftNegligible
  rightNegligible := T.rightNegligible
  advantage_le := T.advantage_le

end CertifiedBinaryReduction
end CryptoLogic.General
