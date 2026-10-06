import Foundation.Crypto.Logic.General.Execution
import Foundation.Crypto.Semantics.Machine.Masking
import Foundation.Crypto.Semantics.Oracle.WholeAttack
import Foundation.Constructions.Symmetric.PRGResource

/-! Concrete adapters preserve the original operational predicates. Different
backends keep their own time units and resource profiles. The common logic
never identifies those units or invents a simulation between machines. -/
namespace CryptoLogic.General.Backends

open Machine
open Foundation.Symmetric

inductive Kind where
  | native | masking | interactive
  deriving DecidableEq, Repr, Encodable

def Code : Kind → Type
  | .native => Machine.Program
  | .masking => Machine.Masking.Code
  | .interactive => CryptoOracle.Interactive.Code

inductive Primitive : Kind → Kind → Type where
  | native (compiler : Machine.ProgramCompiler) : Primitive .native .native
  | mask (side : Bool) : Primitive .native .masking
  | interactive (compiler : CryptoOracle.Interactive.Compiler) : Primitive .interactive .interactive


def Primitive.encode {m n} : Primitive m n →
    Machine.ProgramCompiler ⊕ (Bool ⊕ CryptoOracle.Interactive.Compiler)
  | .native compiler => .inl compiler
  | .mask side => .inr (.inl side)
  | .interactive compiler => .inr (.inr compiler)

def Primitive.decode (m n : Kind) :
    Machine.ProgramCompiler ⊕ (Bool ⊕ CryptoOracle.Interactive.Compiler) → Option (Primitive m n) :=
  match m, n with
  | .native, .native => fun code => match code with | .inl c => some (.native c) | _ => none
  | .native, .masking => fun code => match code with | .inr (.inl b) => some (.mask b) | _ => none
  | .interactive, .interactive => fun code => match code with
      | .inr (.inr c) => some (.interactive c) | _ => none
  | _, _ => fun _ => none

instance (m n : Kind) : Encodable (Primitive m n) :=
  Encodable.ofLeftInjection Primitive.encode (Primitive.decode m n) (by intro p; cases p <;> rfl)

def system : CodeSystem where
  Machine := Kind
  Code := Code
  machineEncodable := inferInstance
  Primitive := Primitive
  codeEncodable := fun kind => by cases kind <;> dsimp [Code] <;> exact inferInstance
  primitiveEncodable := fun _ _ => inferInstance
  runPrimitive := fun primitive code => match primitive with
    | .native compiler => compiler.run code
    | .mask side => Machine.Masking.compile side code
    | .interactive compiler => compiler.run code

/-- The old bit-machine object retains all-input polynomial stopping bounds. -/
def nativeObject (X : CryptoLogic.SecurityObject.{u, v, w}) :
    General.SecurityObject.{u, 0} system .native where
  goal := X.goal
  execution := {
    Resources := Nat → Nat
    ExecutesWithin := fun _ code budget => PolynomiallyBounded budget ∧
      ∀ input, Machine.HaltsWithin code input (budget input.length)
    Realizes := fun F A code budget => X.interface.Realizes F code budget A }
  adversaries := X.adversaries
  represented := by
    intro F A hA
    obtain ⟨p, hr⟩ := X.represented F A hA
    exact ⟨p.program, p.budget, ⟨p.polynomial, p.halts⟩, hr⟩

namespace Native

variable {X Y : CryptoLogic.SecurityObject.{u, v, w}}

def witness (W : X.Witness F A) : (nativeObject X).Witness F A :=
  ⟨W.bounded.program, W.bounded.budget, ⟨W.bounded.polynomial, W.bounded.halts⟩,
    W.realizes, W.admissible⟩

def original (W : (nativeObject X).Witness F A) : X.Witness F A :=
  ⟨⟨W.code, W.resources, W.executes.1, W.executes.2⟩, W.realizes, W.admissible⟩

@[simp] theorem original_witness (W : X.Witness F A) : original (witness W) = W := by cases W; rfl
@[simp] theorem witness_original (W : (nativeObject X).Witness F A) : witness (original W) = W := by cases W; rfl

def reduction (T : CryptoLogic.CertifiedReduction X Y) :
    General.CertifiedReduction (nativeObject X) (nativeObject Y) where
  reduction := T.reduction
  compiler := .primitive (.native T.compiler)
  mapWitness := fun _ _ W => witness (T.mapWitness (original W))
  code_eq := by intros; rfl
  negligible := T.negligible

def transform (T : CryptoLogic.CertifiedTransform X Y) :
    General.CertifiedTransform (nativeObject X) (nativeObject Y) where
  transform := T.transform
  compiler := .primitive (.native T.compiler)
  mapWitness := fun _ _ W => witness (T.mapWitness (original W))
  code_eq := by intros; rfl

def binary {Z : CryptoLogic.SecurityObject.{u, v, w}}
    (T : CryptoLogic.CertifiedBinaryReduction X Y Z) :
    General.CertifiedBinaryReduction (nativeObject X) (nativeObject Y) (nativeObject Z) where
  left := transform T.left
  right := transform T.right
  leftLoss := T.leftLoss
  rightLoss := T.rightLoss
  leftNegligible := T.leftNegligible
  rightNegligible := T.rightNegligible
  advantage_le := T.advantage_le

end Native

/-- Exact full-time/query interface of the interactive oracle machine. -/
noncomputable def interactiveObject {Request Response State : Type u}
    {P : CryptoOracle.Protocol Request Response State}
    (J : CryptoOracle.WholeInterface P) (time queries : Nat → Nat) :
    General.SecurityObject.{u, 0} system .interactive where
  goal := CryptoOracle.goal P
  execution := {
    Resources := Unit
    ExecutesWithin := fun F code _ =>
      (∀ n right, CryptoOracle.Interactive.HaltsWithin code
        (J.bitOracle (CryptoOracle.WholeInterface.world P n (F n) right))
        (CryptoOracle.Interactive.Configuration.initial
          (CryptoOracle.WholeInterface.initialState P n (F n) right) (J.input n (F n))) (time n)) ∧
      (∀ n right finish, finish ∈ (J.execution code n (F n) right (time n)).support →
        finish.reverseTrace.length ≤ queries n)
    Realizes := fun F A code _ => ∀ n right,
      (J.execution code n (F n) right (time n)).map CryptoOracle.Interactive.observe =
        ((A n).run (CryptoOracle.WholeInterface.world P n (F n) right)
          (CryptoOracle.WholeInterface.initialState P n (F n) right)).map J.encodeOutcome }
  adversaries := CryptoOracle.wholeClass J time queries
  represented := by
    intro F A ⟨W⟩
    exact ⟨W.code, (), ⟨W.halts, W.queries⟩, W.realizes⟩

namespace Interactive

variable {Request Response State : Type u} {P : CryptoOracle.Protocol Request Response State}
  {J : CryptoOracle.WholeInterface P} {time queries : Nat → Nat}

def witness (W : CryptoOracle.WholeWitness J time queries F A) :
    (interactiveObject J time queries).Witness F A :=
  ⟨W.code, (), ⟨W.halts, W.queries⟩, W.realizes, ⟨W⟩⟩

def original (W : (interactiveObject J time queries).Witness F A) :
    CryptoOracle.WholeWitness J time queries F A :=
  ⟨W.code, W.executes.1, W.executes.2, W.realizes⟩

@[simp] theorem original_witness (W : CryptoOracle.WholeWitness J time queries F A) :
    original (witness W) = W := by cases W; rfl

noncomputable def reduction {Request' Response' State' : Type u}
    {Q : CryptoOracle.Protocol Request' Response' State'} {JQ : CryptoOracle.WholeInterface Q}
    {r : Reduction (CryptoOracle.goal P) (CryptoOracle.goal Q)} {targetTime targetQueries : Nat → Nat}
    (T : CryptoOracle.WholeReduction P Q r J JQ time queries targetTime targetQueries)
    (hLoss : r.loss.PreservesNegligible) :
    General.CertifiedReduction (interactiveObject J time queries)
      (interactiveObject JQ targetTime targetQueries) where
  reduction := r
  compiler := .primitive (.interactive T.compiler)
  mapWitness := fun F A W => witness (T.mapWitness F A (original W))
  code_eq := by intro F A W; exact T.code_eq F A (original W)
  negligible := hLoss

end Interactive

/-- One-challenge native execution with the original all-challenge guarantee. -/
noncomputable def prgNativeObject (G : Generator) (time : Nat → Nat) :
    General.SecurityObject.{0, 0} system .native where
  goal := G.encryptionGoal
  execution := {
    Resources := Unit
    ExecutesWithin := fun F code _ => ∀ n (challenge : Bits (G.outputLength n)),
      Masking.HaltsWithin (.native code)
        (Masking.initial (.native code) (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) (time n)
    Realizes := fun F A code _ => ∀ n (challenge : Bits (G.outputLength n)),
      Masking.output (.native code)
        (Masking.initial (.native code) (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) (time n) = (A n challenge).map some }
  adversaries := G.nativeClass time
  represented := by
    intro F A ⟨W⟩
    exact ⟨W.program, (), W.halts, W.realizes⟩

/-- The same typed goal, now realized by the finite masking controller. -/
noncomputable def prgMaskingObject (G : Generator) (time : Nat → Nat) :
    General.SecurityObject.{0, 0} system .masking where
  goal := G.prgGoal
  execution := {
    Resources := Unit
    ExecutesWithin := fun F code _ => ∀ n (challenge : Bits (G.outputLength n)),
      Masking.HaltsWithin code
        (Masking.initial code (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) (time n)
    Realizes := fun F A code _ => ∀ n (challenge : Bits (G.outputLength n)),
      Masking.output code
        (Masking.initial code (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) (time n) = (A n challenge).map some }
  adversaries := G.challengeClass time
  represented := by
    intro F A ⟨W⟩
    exact ⟨W.code, (), W.halts, W.realizes⟩

namespace PRG

variable {G : Generator} {time : Nat → Nat}

def nativeWitness (W : G.NativeWitness time F A) : (prgNativeObject G time).Witness F A :=
  ⟨W.program, (), W.halts, W.realizes, ⟨W⟩⟩

def nativeOriginal (W : (prgNativeObject G time).Witness F A) : G.NativeWitness time F A :=
  ⟨W.code, W.executes, W.realizes⟩

def maskingWitness (W : G.ChallengeWitness time F A) : (prgMaskingObject G time).Witness F A :=
  ⟨W.code, (), W.halts, W.realizes, ⟨W⟩⟩

def maskingOriginal (W : (prgMaskingObject G time).Witness F A) : G.ChallengeWitness time F A :=
  ⟨W.code, W.executes, W.realizes⟩

@[simp] theorem nativeOriginal_witness (W : G.NativeWitness time F A) :
    nativeOriginal (nativeWitness W) = W := by cases W; rfl
@[simp] theorem maskingOriginal_witness (W : G.ChallengeWitness time F A) :
    maskingOriginal (maskingWitness W) = W := by cases W; rfl

/-- Adapter only: registration as a cryptographic inference is separate. -/
noncomputable def transform (G : Generator) (time : Nat → Nat) (side : Bool) :
    General.CertifiedTransform (prgNativeObject G time) (prgMaskingObject G (G.reductionTime time)) where
  transform := ⟨fun I => I, fun I A => G.reduce I side A⟩
  compiler := .primitive (.mask side)
  mapWitness := fun F A W => maskingWitness (G.mapWitness time side F A (nativeOriginal W))
  code_eq := by intros; rfl

end PRG
end CryptoLogic.General.Backends
