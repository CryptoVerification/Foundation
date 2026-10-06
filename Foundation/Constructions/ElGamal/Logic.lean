import Foundation.Constructions.ElGamal.MachineSecurity
import Foundation.Crypto.Meta.Soundness

/-! The native ElGamal-to-DDH compiler as a primitive of the small logic.
The source object keeps the nonvacuous reachable-request class. Polynomial
runtime witnesses are selected only for analysis; generated code is the existing
fixed native compiler and never inspects those witnesses. -/

namespace ElGamal.Logic

open CryptoLogic Machine

variable
  {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
  {X : Nat → Type 1} {embed : ∀ n, X n → ConcreteInstance sampling n}

noncomputable def indCPAObject (M : RepresentedSimulatorPrimitives sampling X embed) :
    SecurityObject where
  goal := representedINDCPAGoal sampling X embed
  interface := representedINDCPAElementInterface sampling X embed M.instanceCode M.elementCode
  adversaries := representedINDCPAElementPPTClass sampling X embed M.instanceCode M.elementCode
  represented := by
    intro F A h
    obtain ⟨p, q, _size, hq, hHalts, _hSize, _hChoose, _hGuess, hRealizes⟩ := h
    exact ⟨⟨p, q, hq, hHalts⟩, hRealizes⟩

noncomputable def ddhObject (M : RepresentedSimulatorPrimitives sampling X embed) :
    SecurityObject :=
  SecurityObject.ppt (representedDDHGoal sampling X embed)
    (representedDDHInterface sampling X embed M.instanceCode
      (fun n x => (M.elementCode n x).triple))

/-- The analysis witness is independent of the instance family. It bounds all
finite inputs, including malformed requests, for exactly the native output code. -/
noncomputable def nativeBounded {M : RepresentedSimulatorPrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M) (p : BoundedProgram) : BoundedProgram where
  program := N.simulatorCode p.program
  budget := Classical.choose (N.nativeSimulator_polynomialTime
    p.program p.budget p.polynomial p.halts)
  polynomial := (Classical.choose_spec (N.nativeSimulator_polynomialTime
    p.program p.budget p.polynomial p.halts)).1
  halts := (Classical.choose_spec (N.nativeSimulator_polynomialTime
    p.program p.budget p.polynomial p.halts)).2

/-- A primitive with real code, all-input polynomial runtime, exact adversary
realization, reachable-class preservation, and identity advantage loss. -/
noncomputable def certificate {M : RepresentedSimulatorPrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M) : CertifiedReduction (indCPAObject M) (ddhObject M) where
  reduction := representedReduction sampling X embed
  compiler := N.simulatorCompiler
  budget := fun p => (nativeBounded N p).budget
  polynomial := fun p => (nativeBounded N p).polynomial
  halts := fun p => (nativeBounded N p).halts
  realizes := by
    intro F A p h
    exact N.nativeSimulator_realizes F A p.program p.budget (nativeBounded N p).budget
      p.halts h (fun n x first second last => (nativeBounded N p).halts _)
  admissibility := N.nativeSimulator_preservesAdmissibility
  negligible := AdvantageBound.id_preservesNegligible

inductive Object where
  | indCPA
  | ddh
  deriving DecidableEq, Repr

inductive Primitive : Object → Object → Type where
  | elGamalToDDH : Primitive .indCPA .ddh

/-- Only fixed finite code belongs to the executable language. -/
def language (normalizer multiply : Program) : Language where
  Object := Object
  Primitive := Primitive
  primitiveCompiler := fun e => match e with
    | .elGamalToDDH => .chooseChallenge normalizer multiply

noncomputable def signature {M : RepresentedSimulatorPrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M) : Signature (language N.program M.multiplyProgram) where
  interpret
    | .indCPA => indCPAObject M
    | .ddh => ddhObject M
  certificate := fun e => match e with
    | .elGamalToDDH => certificate N
  compiler_eq := by intro _ _ e; cases e; rfl

def reductionExpr (normalizer multiply : Program) :
    ReductionExpr (language normalizer multiply) .indCPA .ddh :=
  .primitive .elGamalToDDH

/-- DDH hardness is a context assumption on exactly the mapped family. -/
noncomputable def context {M : RepresentedSimulatorPrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed)) : Context (signature N) :=
  [⟨.ddh, (representedReduction sampling X embed).mapFamily F⟩]

def derivation {M : RepresentedSimulatorPrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed)) :
    Derivation (signature N) (context N F) .indCPA F where
  code := .transport (reductionExpr N.program M.multiplyProgram) (.hypothesis ⟨0, by simp [context]⟩)
  compiler := .comp (reductionExpr N.program M.multiplyProgram).compiler .identity
  compiler_eq := rfl
  typed := ⟨DerivationTree.transport (S := signature N) (Γ := context N F)
    (reductionExpr N.program M.multiplyProgram) F (.hypothesis ⟨0, by simp [context]⟩), rfl⟩

/-- The extracted compiler emits precisely the existing native simulator.
Neither a security hypothesis nor a runtime witness enters this code equality. -/
theorem derivation_compiler_run {M : RepresentedSimulatorPrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed)) (p : Program) :
    (derivation N F).compiler.run p = N.simulatorCode p := rfl

theorem derivation_selected {M : RepresentedSimulatorPrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed)) :
    (derivation N F).extract.index.val = 0 := rfl

/-- Recover the native machine security theorem through the logic's generic
soundness theorem, retaining the exact source and target adversary classes. -/
theorem secure_of_ddh {M : RepresentedSimulatorPrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (hDDH : (ddhObject M).Secure ((representedReduction sampling X embed).mapFamily F)) :
    (indCPAObject M).Secure F :=
  (derivation N F).sound_of_selected hDDH

/-- The instantiated logical compiler has a returned polynomial stopping
budget on every raw input, not only inputs reached in the security game. -/
theorem extracted_halts {M : RepresentedSimulatorPrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (p : BoundedProgram) (input : List Bool) :
    HaltsWithin (N.simulatorCode p.program) input
      (((derivation N F).runBounded p).budget input.length) :=
  (derivation N F).compiler_halts p input

end ElGamal.Logic
