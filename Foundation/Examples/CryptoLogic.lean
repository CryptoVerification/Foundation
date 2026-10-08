import Foundation.Crypto.Meta.Soundness
import Foundation.Examples.MachineProgramTransformation
import Foundation.Constructions.ElGamal.PrimeOrderLogic

namespace CryptoLogic.Examples

open Machine Machine.Examples

inductive Object where
  | source
  | middle
  | target
  deriving DecidableEq, Repr

inductive Primitive : Object → Object → Type where
  | append : Primitive .source .middle
  | constant : Primitive .middle .target
  | guard : Primitive .target .target

/-- Three syntactically distinct objects with the existing toy machine goal.
Different code transformations make compiler order observable. -/
def language : Language where
  Object := Object
  Primitive := Primitive
  primitiveCompiler := fun e => match e with
    | .append => .suffix [.halt]
    | .constant => constantAnswerCompiler
    | .guard => .guarded

noncomputable def signature : Signature language where
  interpret := fun _ => SecurityObject.ppt bitGoal bitInterface
  certificate := fun e => match e with
    | .append => CertifiedReduction.ofTransformation bitInterface bitInterface
        (Reduction.id bitGoal) appendHaltTransformation AdvantageBound.id_preservesNegligible
    | .constant => CertifiedReduction.ofTransformation bitInterface bitInterface
        constantAnswerReduction constantAnswerTransformation AdvantageBound.id_preservesNegligible
    | .guard => CertifiedReduction.ofTransformation bitInterface bitInterface
        (Reduction.id bitGoal) (Reduction.MachineProgramTransformation.guarded bitInterface)
        AdvantageBound.id_preservesNegligible
  compiler_eq := by intro _ _ e; cases e <;> rfl

def route : ReductionExpr language .source .target :=
  .seq (.primitive .append) (.primitive .constant)

/-- The first assumption is unused; extraction must select position one. -/
def context : Context signature :=
  [⟨.middle, bitFamily⟩, ⟨.target, bitFamily⟩]

/-- Use the public rules with a noncomputable signature, rather than constructing
records by hand. These definitions must remain executable. -/
def targetHypothesis : Derivation signature context .target bitFamily :=
  Derivation.hypothesis (S := signature) (Γ := context) ⟨1, by decide⟩

def derivation : Derivation signature context .source bitFamily :=
  Derivation.transport (S := signature) (Γ := context) route bitFamily targetHypothesis

example : derivation.extract.index.val = 1 := rfl

/-- Append runs first and is then replaced by the constant compiler. Reversing
that order would instead leave two halt instructions. -/
example : derivation.compiler.run randomOutputBit = haltImmediately := rfl

example : derivation.compiler.runCode (Program.encode randomOutputBit) =
    some (Program.encode haltImmediately) := by
  rw [ProgramCompiler.runCode_encode]
  rfl

def sourceProgram : BoundedProgram where
  program := randomOutputBit
  budget := fun _ => 2
  polynomial := PolynomiallyBounded.const 2
  halts := randomOutputBit_haltsWithin_any

example (m : Nat) : (route.eval signature).budget sourceProgram m = 1 := rfl

noncomputable def sourceWitness : (signature.interpret .source).Witness bitFamily
    (bitInterface.realizeFamily bitFamily randomOutputBit (fun _ => 2)) where
  bounded := sourceProgram
  realizes := rfl
  admissible := randomOutputBit_ppt

example : (derivation.mapWitness sourceWitness).bounded.program = haltImmediately := by
  exact (derivation.mapWitness_program sourceWitness).trans rfl
example : PolynomiallyBounded (derivation.mapWitness sourceWitness).bounded.budget :=
  (derivation.mapWitness sourceWitness).bounded.polynomial

example : PolynomiallyBounded (derivation.runBounded sourceProgram).budget :=
  (derivation.runBounded sourceProgram).polynomial

example (input : List Bool) :
    HaltsWithin (derivation.compiler.run randomOutputBit) input
      ((derivation.runBounded sourceProgram).budget input.length) :=
  derivation.compiler_halts sourceProgram input

example (hTarget : (signature.interpret .target).Secure bitFamily) :
    (signature.interpret .source).Secure bitFamily :=
  derivation.sound_of_selected hTarget

example : ¬ Nonempty (Derivation signature [] .source bitFamily) := by
  rintro ⟨d⟩
  exact d.no_empty

def replacementContext : Context signature :=
  [⟨.target, bitFamily⟩, ⟨.middle, bitFamily⟩]

def guardedRoute : ReductionExpr language .target .target :=
  .primitive .guard

example (m : Nat) : ((route.seq guardedRoute).eval signature).budget sourceProgram m =
    GuardedCompiler.rawTraceBudget (fun _ => 1) m := rfl

def guardedDerivation :
    Derivation signature replacementContext .target bitFamily :=
  Derivation.transport (S := signature) (Γ := replacementContext) guardedRoute bitFamily
    (Derivation.hypothesis (S := signature) (Γ := replacementContext) ⟨0, by decide⟩)

/-- Replace the used assumption by a nontrivial guarded derivation, and move
it to position zero. Both dependency selection and emitted code must change. -/
def replacement (i : Fin context.length) :
    Derivation signature replacementContext (context[i]).object (context[i]).family :=
  match i with
  | ⟨0, _⟩ => Derivation.hypothesis (S := signature) (Γ := replacementContext)
      ⟨1, by decide⟩
  | ⟨1, _⟩ => guardedDerivation
  | ⟨n + 2, h⟩ => False.elim (by simp [context] at h)

def substituted : Derivation signature replacementContext .source bitFamily :=
  derivation.substitute replacement

example : substituted.extract.index.val = 0 := rfl
example : substituted.compiler.run randomOutputBit =
    GuardedCompiler.rawCompile haltImmediately := rfl
example : (substituted.mapWitness sourceWitness).bounded.program =
    GuardedCompiler.rawCompile haltImmediately := by
  exact (substituted.mapWitness_program sourceWitness).trans rfl
example : PolynomiallyBounded (substituted.mapWitness sourceWitness).bounded.budget :=
  (substituted.mapWitness sourceWitness).bounded.polynomial

example (h : replacementContext.Valid) : (signature.interpret .source).Secure bitFamily :=
  substituted.sound h

/- Kernel evaluation of the executable compiler interpreter is independent
of the signature's noncomputable semantic interpretation. -/
#guard (ProgramCompiler.comp (.suffix [.halt]) (.constant [.halt])).run [] = [.halt]
#guard (ProgramCompiler.comp (.constant [.halt]) (.suffix [.halt])).run [] = [.halt, .halt]

/- Run the actual derivation's compiler using Lean's executable evaluator.
The noncomputable semantic signature is absent from this computation. -/
/-- info: true -/
#guard_msgs in
#eval targetHypothesis.compiler.run randomOutputBit == randomOutputBit
/-- info: true -/
#guard_msgs in
#eval derivation.compiler.run randomOutputBit == haltImmediately
/-- info: true -/
#guard_msgs in
#eval substituted.compiler.run randomOutputBit == GuardedCompiler.rawCompile haltImmediately

/- The executable ElGamal language takes code directly, without a semantic
representation certificate. Small payloads exercise the full compiler evaluator. -/
/-- info: true -/
#guard_msgs in
#eval ((ElGamal.Logic.reductionExpr [.halt] [.halt]).compiler.run []).length == 1900

/-- This must compile as a computable definition despite the noncomputable
concrete interpretation and arbitrary instance-family parameter. -/
def concreteCompilerForFamily
    (F : InstanceFamily (ElGamal.representedINDCPAGoal
      ElGamal.PrimeOrderRepresentation.sampling ElGamal.PrimeOrderRepresentation.Domain
      ElGamal.PrimeOrderRepresentation.embed)) : ProgramCompiler :=
  (ElGamal.PrimeOrderRepresentation.logicDerivation F).compiler

example (F) : concreteCompilerForFamily F =
    ElGamal.PrimeOrderRepresentation.logicCompiler := rfl

/-- The emitted concrete code is definitionally the existing native simulator.
This checks the computable wrapper without materializing its very large code. -/
example (F) (source : Program) :
    (concreteCompilerForFamily F).run source =
      ElGamal.PrimeOrderRepresentation.chooseNormalizer.simulatorCode source := rfl

end CryptoLogic.Examples
