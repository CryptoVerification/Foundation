import Foundation.Crypto.Semantics.Machine.CertifiedReduction

namespace CryptoLogic

universe u v w

/-- An adversary transformation without a single-target advantage inequality. -/
structure AdversaryTransform (P Q : CryptoGoal.{u}) where
  mapInstance : ∀ {n}, P.Instance n → Q.Instance n
  reduce : ∀ {n} (I : P.Instance n), P.Adversary n I → Q.Adversary n (mapInstance I)

namespace AdversaryTransform

abbrev mapFamily {P Q} (t : AdversaryTransform P Q) (F : InstanceFamily P) : InstanceFamily Q :=
  fun n => t.mapInstance (F n)

def mapAdversaryFamily {P Q} (t : AdversaryTransform P Q) (F : InstanceFamily P)
    (A : AdversaryFamily P F) : AdversaryFamily Q (t.mapFamily F) :=
  fun n => t.reduce (F n) (A n)

end AdversaryTransform

/-- A branch implements an adversary transformation and certifies its resources.
It deliberately does not assert that this branch alone proves security. -/
structure CertifiedTransform (X Y : SecurityObject.{u, v, w}) where
  transform : AdversaryTransform X.goal Y.goal
  compiler : Machine.ProgramCompiler
  budget : BoundedProgram → Nat → Nat
  polynomial : ∀ p, PolynomiallyBounded (budget p)
  halts : ∀ p input, Machine.HaltsWithin (compiler.run p.program) input (budget p input.length)
  realizes : ∀ F A (p : BoundedProgram), X.interface.Realizes F p.program p.budget A →
    Y.interface.Realizes (transform.mapFamily F) (compiler.run p.program) (budget p)
      (transform.mapAdversaryFamily F A)
  admissible : ∀ F A, X.adversaries.admissible F A →
    Y.adversaries.admissible (transform.mapFamily F) (transform.mapAdversaryFamily F A)

namespace CertifiedTransform

abbrev ofReduction {X Y} (r : CertifiedReduction X Y) : CertifiedTransform X Y where
  transform := ⟨r.reduction.mapInstance, r.reduction.reduce⟩
  compiler := r.compiler
  budget := r.budget
  polynomial := r.polynomial
  halts := r.halts
  realizes := r.realizes
  admissible := r.admissibility.preserves

def runBounded {X Y} (t : CertifiedTransform X Y) (p : BoundedProgram) : BoundedProgram :=
  ⟨t.compiler.run p.program, t.budget p, t.polynomial p, t.halts p⟩

def mapWitness {X Y} (t : CertifiedTransform X Y) {F A} (p : X.Witness F A) :
    Y.Witness (t.transform.mapFamily F) (t.transform.mapAdversaryFamily F A) :=
  ⟨t.runBounded p.bounded, t.realizes F A p.bounded p.realizes, t.admissible F A p.admissible⟩

def comp {X Y Z} (r : CertifiedTransform X Y) (s : CertifiedTransform Y Z) :
    CertifiedTransform X Z where
  transform := {
    mapInstance := fun I => s.transform.mapInstance (r.transform.mapInstance I)
    reduce := fun I A => s.transform.reduce (r.transform.mapInstance I) (r.transform.reduce I A) }
  compiler := .comp r.compiler s.compiler
  budget := fun p => s.budget (r.runBounded p)
  polynomial := fun p => s.polynomial (r.runBounded p)
  halts := fun p => s.halts (r.runBounded p)
  realizes := fun F A p h => s.realizes _ _ (r.runBounded p) (r.realizes F A p h)
  admissible := fun F A h => s.admissible _ _ (r.admissible F A h)

end CertifiedTransform

/-- Two independently executable branches and one joint quantitative bound.
No independence of games, random coins, or assumptions is postulated. -/
structure CertifiedBinaryReduction (X Y Z : SecurityObject.{u, v, w}) where
  left : CertifiedTransform X Y
  right : CertifiedTransform X Z
  leftLoss : AdvantageBound
  rightLoss : AdvantageBound
  leftNegligible : leftLoss.PreservesNegligible
  rightNegligible : rightLoss.PreservesNegligible
  advantage_le : ∀ F A n, advantageProfile X.goal F A n ≤
    leftLoss.eval n (advantageProfile Y.goal (left.transform.mapFamily F)
      (left.transform.mapAdversaryFamily F A) n) +
    rightLoss.eval n (advantageProfile Z.goal (right.transform.mapFamily F)
      (right.transform.mapAdversaryFamily F A) n)

namespace CertifiedBinaryReduction

theorem secure {X Y Z} (r : CertifiedBinaryReduction X Y Z) (F : InstanceFamily X.goal)
    (hY : Y.Secure (r.left.transform.mapFamily F))
    (hZ : Z.Secure (r.right.transform.mapFamily F)) : X.Secure F := by
  intro A hA
  have hl := r.leftNegligible _ (hY _ (r.left.admissible F A hA))
  have hr := r.rightNegligible _ (hZ _ (r.right.admissible F A hA))
  exact Negligible.mono (r.advantage_le F A) (hl.add hr)

end CertifiedBinaryReduction
end CryptoLogic
