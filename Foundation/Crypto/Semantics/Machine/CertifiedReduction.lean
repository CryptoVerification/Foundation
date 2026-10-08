import Foundation.Crypto.Semantics.Machine.ProgramTransformation
import Foundation.Crypto.Semantics.Security.Reduction

/-! Certificates used by the small security logic. Runtime budgets are analysis
data; only `ProgramCompiler` constructs executable code. In particular, a budget
may depend on a valid source stopping certificate, rather than just the value of
the source budget at the target's original input length. -/

namespace CryptoLogic

open Machine

universe u v w

/-- One finite program and an all-input, all-random-branch polynomial stopping
budget. The budget is measured in total input bit length. -/
structure BoundedProgram where
  program : Program
  budget : Nat → Nat
  polynomial : PolynomiallyBounded budget
  halts : ∀ input : List Bool, HaltsWithin program input (budget input.length)

namespace BoundedProgram

theorem polynomialTime (p : BoundedProgram) : PolynomialTime p.program :=
  ⟨p.budget, p.polynomial, p.halts⟩

end BoundedProgram

set_option linter.checkUnivs false in
/-- A semantic object of the logic. The class retains its protocol-specific
input-size conditions. `represented` rules out admitting families with no
finite polynomial-time machine realization; it does not assert that the class
is inhabited or certify the external adapter's computational cost. -/
structure SecurityObject where
  goal : CryptoGoal.{u}
  interface : MachineAdversaryInterface.{u, v, w} goal
  adversaries : AdversaryClass goal
  represented : ∀ (F : InstanceFamily goal) (A : AdversaryFamily goal F),
    adversaries.admissible F A →
      ∃ p : BoundedProgram, interface.Realizes F p.program p.budget A

namespace SecurityObject

/-- The existing all-request PPT class, including its input-size witness. -/
noncomputable def ppt (P : CryptoGoal.{u})
    (J : MachineAdversaryInterface.{u, v, w} P) : SecurityObject.{u, v, w} where
  goal := P
  interface := J
  adversaries := J.pptClass
  represented := by
    intro F A h
    obtain ⟨p, q, _size, hq, hHalts, _hSize, hRealizes⟩ := h
    exact ⟨⟨p, q, hq, hHalts⟩, hRealizes⟩

/-- A realization certificate for an admitted adversary. The class membership
keeps the protocol-size conditions alongside the actual code and its budget. -/
structure Witness (X : SecurityObject.{u, v, w})
    (F : InstanceFamily X.goal) (A : AdversaryFamily X.goal F) where
  bounded : BoundedProgram
  realizes : X.interface.Realizes F bounded.program bounded.budget A
  admissible : X.adversaries.admissible F A

theorem witness_nonempty (X : SecurityObject.{u, v, w})
    (F : InstanceFamily X.goal) (A : AdversaryFamily X.goal F)
    (h : X.adversaries.admissible F A) : Nonempty (X.Witness F A) := by
  obtain ⟨p, hp⟩ := X.represented F A h
  exact ⟨⟨p, hp, h⟩⟩

def Secure (X : SecurityObject.{u, v, w}) (F : InstanceFamily X.goal) : Prop :=
  SecureOnWithin X.goal X.adversaries F

end SecurityObject

/-- A quantitative reduction with a finite compiler and a polynomial stopping
budget for exactly its emitted code. Runtime analysis may be noncomputable;
the compiler receives only source code, never a family or analysis witness.
Class preservation and negligible-loss preservation are separate obligations. -/
structure CertifiedReduction (X Y : SecurityObject.{u, v, w}) where
  reduction : Reduction X.goal Y.goal
  compiler : ProgramCompiler
  budget : BoundedProgram → Nat → Nat
  polynomial : ∀ p, PolynomiallyBounded (budget p)
  halts : ∀ p (input : List Bool),
    HaltsWithin (compiler.run p.program) input (budget p input.length)
  realizes : ∀ (F : InstanceFamily X.goal) (A : AdversaryFamily X.goal F)
    (p : BoundedProgram), X.interface.Realizes F p.program p.budget A →
      Y.interface.Realizes (reduction.mapFamily F) (compiler.run p.program)
        (budget p) (reduction.mapAdversaryFamily F A)
  admissibility : reduction.PreservesAdmissibility X.adversaries Y.adversaries
  negligible : reduction.loss.PreservesNegligible

namespace CertifiedReduction

def runBounded {X Y : SecurityObject.{u, v, w}}
    (r : CertifiedReduction X Y) (p : BoundedProgram) : BoundedProgram where
  program := r.compiler.run p.program
  budget := r.budget p
  polynomial := r.polynomial p
  halts := r.halts p

def mapWitness {X Y : SecurityObject.{u, v, w}}
    (r : CertifiedReduction X Y) {F : InstanceFamily X.goal}
    {A : AdversaryFamily X.goal F} (p : X.Witness F A) :
    Y.Witness (r.reduction.mapFamily F) (r.reduction.mapAdversaryFamily F A) where
  bounded := r.runBounded p.bounded
  realizes := r.realizes F A p.bounded p.realizes
  admissible := r.admissibility.preserves F A p.admissible

def id (X : SecurityObject.{u, v, w}) : CertifiedReduction X X where
  reduction := Reduction.id X.goal
  compiler := .identity
  budget := fun p => p.budget
  polynomial := fun p => p.polynomial
  halts := fun p => p.halts
  realizes := by intro F A p h; exact h
  admissibility := Reduction.id_preservesAdmissibility X.goal X.adversaries
  negligible := AdvantageBound.id_preservesNegligible

def comp {X Y Z : SecurityObject.{u, v, w}}
    (r : CertifiedReduction X Y) (s : CertifiedReduction Y Z) :
    CertifiedReduction X Z where
  reduction := r.reduction.comp s.reduction
  compiler := .comp r.compiler s.compiler
  budget := fun p => s.budget (r.runBounded p)
  polynomial := fun p => s.polynomial (r.runBounded p)
  halts := fun p => s.halts (r.runBounded p)
  realizes := by
    intro F A p h
    exact s.realizes (r.reduction.mapFamily F)
      (r.reduction.mapAdversaryFamily F A) (r.runBounded p) (r.realizes F A p h)
  admissibility := Reduction.comp_preservesAdmissibility r.reduction s.reduction
    X.adversaries Y.adversaries Z.adversaries r.admissibility s.admissibility
  negligible := AdvantageBound.comp_preservesNegligible _ _ r.negligible s.negligible

theorem secure {X Y : SecurityObject.{u, v, w}}
    (r : CertifiedReduction X Y) (F : InstanceFamily X.goal)
    (h : Y.Secure (r.reduction.mapFamily F)) : X.Secure F :=
  r.reduction.secureOnWithin X.adversaries Y.adversaries F
    r.admissibility r.negligible h

/-- Reuse a same-input simulation certificate with independently proved class
preservation. No all-request input-size condition is imposed on the source. -/
def ofSimulation {X Y : SecurityObject.{u, v, w}}
    (R : Reduction X.goal Y.goal)
    (T : R.MachineProgramSimulation X.interface Y.interface)
    (hAdm : R.PreservesAdmissibility X.adversaries Y.adversaries)
    (hLoss : R.loss.PreservesNegligible) : CertifiedReduction X Y where
  reduction := R
  compiler := T.compiler
  budget := fun p => T.transformBudget p.budget
  polynomial := fun p => T.budget_polynomiallyBounded p.polynomial
  halts := fun p => T.halts p.program p.budget p.halts
  realizes := fun F A p h => T.realizes F A p.program p.budget p.halts h
  admissibility := hAdm
  negligible := hLoss

noncomputable def ofTransformation {P Q : CryptoGoal.{u}}
    (JP : MachineAdversaryInterface.{u, v, w} P)
    (JQ : MachineAdversaryInterface.{u, v, w} Q)
    (R : Reduction P Q) (T : R.MachineProgramTransformation JP JQ)
    (hLoss : R.loss.PreservesNegligible) :
    CertifiedReduction (SecurityObject.ppt P JP) (SecurityObject.ppt Q JQ) :=
  ofSimulation R T.toSimulation T.preservesAdmissibility hLoss

end CertifiedReduction
end CryptoLogic
