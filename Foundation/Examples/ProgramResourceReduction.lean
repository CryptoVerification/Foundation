import Foundation.Crypto.Semantics.Resource.ProgramReduction
import Foundation.Examples.UniformReduction
import Foundation.Crypto.Semantics.Security.Reduction

namespace Foundation.Examples.ProgramResourceReduction

open Foundation.Examples.UniformReduction

/-- An abstract resource of the source program, dependent on its parameter. -/
def CP : ProgramResourceMeasure sourceModel where
  profile := fun _ prog n => (show Nat from prog) + n

/-- The target program has a quadratic parameter overhead. -/
def CQ : ProgramResourceMeasure targetModel where
  profile := fun _ prog n => (n + 1) ^ 2 * ((show Nat from prog) + n)

/-- The transformed program is charged directly. Its program parameter rises
by one, which is covered by the source profile's `+ 1`. -/
def B : T.ResourceBound CP CQ where
  coefficient := 1
  securityDegree := 2
  sourceDegree := 1
  bound := by
    intro F prog n
    change (n + 1) ^ 2 * (((show Nat from prog) + 1) + n) ≤
      1 * (n + 1) ^ 2 * (((show Nat from prog) + n) + 1) ^ 1
    have h : ((show Nat from prog) + 1) + n =
        ((show Nat from prog) + n) + 1 := by omega
    rw [h]
    simp

private theorem source_polynomiallyBounded (F : InstanceFamily P)
    (prog : sourceModel.Program F) :
    PolynomiallyBounded (CP.profile F prog) := by
  exact PolynomiallyBounded.add
    (PolynomiallyBounded.const (show Nat from prog)) PolynomiallyBounded.id

/-- The source family is realized by program `3`, which has polynomial
program resource. -/
example (F : InstanceFamily P) :
    (sourceModel.polynomialProgramClass CP).admissible F
      (sourceModel.realize F (3 : Nat)) := by
  exact ⟨(3 : Nat), rfl, source_polynomiallyBounded F (3 : Nat)⟩

/-- Generic preservation uses `T.transform F 3` as the target witness for
both realization and resource boundedness. -/
example (F : InstanceFamily P) :
    (targetModel.polynomialProgramClass CQ).admissible (R.mapFamily F)
      (R.mapAdversaryFamily F (sourceModel.realize F (3 : Nat))) := by
  have hSource : (sourceModel.polynomialProgramClass CP).admissible F
      (sourceModel.realize F (3 : Nat)) :=
    ⟨(3 : Nat), rfl, source_polynomiallyBounded F (3 : Nat)⟩
  exact B.preservesAdmissibility.preserves F _ hSource

example (F : InstanceFamily P) :
    PolynomiallyBounded (CQ.profile (R.mapFamily F) (T.transform F (3 : Nat))) :=
  PolynomiallyBounded.mono (B.bound F (3 : Nat))
    (B.majorant_polynomiallyBounded F (3 : Nat)
      (source_polynomiallyBounded F (3 : Nat)))

/-- Existing security transport accepts the same-witness preservation. -/
example (F : InstanceFamily P)
    (hQ : SecureOnWithin Q (targetModel.polynomialProgramClass CQ) (R.mapFamily F)) :
    SecureOnWithin P (sourceModel.polynomialProgramClass CP) F := by
  exact R.secureOnWithin (sourceModel.polynomialProgramClass CP)
    (targetModel.polynomialProgramClass CQ) F B.preservesAdmissibility
    AdvantageBound.id_preservesNegligible hQ

end Foundation.Examples.ProgramResourceReduction
