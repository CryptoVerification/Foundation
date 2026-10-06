import Foundation.Crypto.Semantics.Machine.BinaryReduction

/-! Machine-independent execution certificates. Executable code and compiler
syntax are countable finite data. Runtime/resource evidence is separate and
may depend on the protocol and public instance family. No execution cost is
assigned by this interface: concrete adapters must supply real certificates. -/
namespace CryptoLogic.General

universe u v

set_option backward.isDefEq.respectTransparency false

/-- A collection of code types and registered, typed compiler primitives.
The evaluator receives only finite syntax and source code. -/
structure CodeSystem where
  Machine : Type
  Code : Machine → Type
  machineEncodable : Encodable Machine
  Primitive : Machine → Machine → Type
  codeEncodable : ∀ m, Encodable (Code m)
  primitiveEncodable : ∀ m n, Encodable (Primitive m n)
  runPrimitive : ∀ {m n}, Primitive m n → Code m → Code n

inductive Compiler (K : CodeSystem) : K.Machine → K.Machine → Type where
  | identity (m) : Compiler K m m
  | primitive {m n} : K.Primitive m n → Compiler K m n
  | comp {m n k} : Compiler K m n → Compiler K n k → Compiler K m k

namespace Compiler

variable {K : CodeSystem}

def run {m n} : Compiler K m n → K.Code m → K.Code n
  | .identity _, code => code
  | .primitive p, code => K.runPrimitive p code
  | .comp first second, code => second.run (first.run code)

@[simp] theorem run_identity (m) (code : K.Code m) : (identity m).run code = code := rfl
@[simp] theorem run_comp {m n k} (first : Compiler K m n) (second : Compiler K n k)
    (code : K.Code m) : (first.comp second).run code = second.run (first.run code) := rfl

theorem comp_assoc_run {m n k l} (first : Compiler K m n) (second : Compiler K n k)
    (third : Compiler K k l) (code : K.Code m) :
    ((first.comp second).comp third).run code = (first.comp (second.comp third)).run code := rfl

end Compiler

/-- Resources are analysis data. `ExecutesWithin` must express the concrete
backend's stopping and resource guarantees; `Realizes` its semantic equality.
Separating them prevents an abstract code generator from inventing a bound. -/
structure ExecutionInterface (K : CodeSystem) (m : K.Machine) (P : CryptoGoal.{u}) where
  Resources : Type v
  ExecutesWithin : InstanceFamily P → K.Code m → Resources → Prop
  Realizes : ∀ F, AdversaryFamily P F → K.Code m → Resources → Prop

set_option linter.checkUnivs false in
structure SecurityObject (K : CodeSystem) (m : K.Machine) where
  goal : CryptoGoal.{u}
  execution : ExecutionInterface.{u, v} K m goal
  adversaries : AdversaryClass goal
  represented : ∀ F A, adversaries.admissible F A →
    ∃ code resources, execution.ExecutesWithin F code resources ∧
      execution.Realizes F A code resources

namespace SecurityObject

variable {K : CodeSystem} {m : K.Machine}

structure Witness (X : SecurityObject.{u, v} K m)
    (F : InstanceFamily X.goal) (A : AdversaryFamily X.goal F) where
  code : K.Code m
  resources : X.execution.Resources
  executes : X.execution.ExecutesWithin F code resources
  realizes : X.execution.Realizes F A code resources
  admissible : X.adversaries.admissible F A

theorem witness_nonempty (X : SecurityObject.{u, v} K m) (F A)
    (h : X.adversaries.admissible F A) : Nonempty (X.Witness F A) := by
  obtain ⟨code, resources, hExec, hReal⟩ := X.represented F A h
  exact ⟨⟨code, resources, hExec, hReal, h⟩⟩

def Secure (X : SecurityObject.{u, v} K m) (F : InstanceFamily X.goal) : Prop :=
  SecureOnWithin X.goal X.adversaries F

end SecurityObject

/-- A typed compiler and evidence for precisely its emitted code. -/
structure CertifiedTransform {K : CodeSystem} {m n : K.Machine}
    (X : SecurityObject.{u, v} K m) (Y : SecurityObject.{u, v} K n) where
  transform : CryptoLogic.AdversaryTransform X.goal Y.goal
  compiler : Compiler K m n
  mapWitness : ∀ F A, X.Witness F A →
    Y.Witness (transform.mapFamily F) (transform.mapAdversaryFamily F A)
  code_eq : ∀ F A W, (mapWitness F A W).code = compiler.run W.code

namespace CertifiedTransform

variable {K : CodeSystem} {m n k : K.Machine}
  {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n}
  {Z : SecurityObject.{u, v} K k}

def id (X : SecurityObject.{u, v} K m) : CertifiedTransform X X where
  transform := ⟨fun I => I, fun _ A => A⟩
  compiler := .identity m
  mapWitness := fun _ _ W => W
  code_eq := by intros; rfl

def comp (first : CertifiedTransform X Y) (second : CertifiedTransform Y Z) :
    CertifiedTransform X Z where
  transform := ⟨fun I => second.transform.mapInstance (first.transform.mapInstance I),
    fun I A => second.transform.reduce (first.transform.mapInstance I) (first.transform.reduce I A)⟩
  compiler := .comp first.compiler second.compiler
  mapWitness := fun F A W => second.mapWitness _ _ (first.mapWitness F A W)
  code_eq := by intros; rw [second.code_eq, first.code_eq]; rfl

theorem admissible (T : CertifiedTransform X Y) (F A)
    (h : X.adversaries.admissible F A) :
    Y.adversaries.admissible (T.transform.mapFamily F) (T.transform.mapAdversaryFamily F A) := by
  obtain ⟨W⟩ := X.witness_nonempty F A h
  exact (T.mapWitness F A W).admissible

theorem compiler_executes (T : CertifiedTransform X Y) (F A) (W : X.Witness F A) :
    Y.execution.ExecutesWithin (T.transform.mapFamily F) (T.compiler.run W.code)
      (T.mapWitness F A W).resources := by
  rw [← T.code_eq]
  exact (T.mapWitness F A W).executes

theorem compiler_realizes (T : CertifiedTransform X Y) (F A) (W : X.Witness F A) :
    Y.execution.Realizes (T.transform.mapFamily F) (T.transform.mapAdversaryFamily F A)
      (T.compiler.run W.code) (T.mapWitness F A W).resources := by
  rw [← T.code_eq]
  exact (T.mapWitness F A W).realizes

end CertifiedTransform

structure CertifiedReduction {K : CodeSystem} {m n : K.Machine}
    (X : SecurityObject.{u, v} K m) (Y : SecurityObject.{u, v} K n) where
  reduction : Reduction X.goal Y.goal
  compiler : Compiler K m n
  mapWitness : ∀ F A, X.Witness F A →
    Y.Witness (reduction.mapFamily F) (reduction.mapAdversaryFamily F A)
  code_eq : ∀ F A W, (mapWitness F A W).code = compiler.run W.code
  negligible : reduction.loss.PreservesNegligible

namespace CertifiedReduction

variable {K : CodeSystem} {m n k : K.Machine}
  {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n}
  {Z : SecurityObject.{u, v} K k}

def toTransform (T : CertifiedReduction X Y) : CertifiedTransform X Y where
  transform := ⟨T.reduction.mapInstance, T.reduction.reduce⟩
  compiler := T.compiler
  mapWitness := T.mapWitness
  code_eq := T.code_eq

def id (X : SecurityObject.{u, v} K m) : CertifiedReduction X X where
  reduction := Reduction.id X.goal
  compiler := .identity m
  mapWitness := fun _ _ W => W
  code_eq := by intros; rfl
  negligible := AdvantageBound.id_preservesNegligible

def comp (first : CertifiedReduction X Y) (second : CertifiedReduction Y Z) :
    CertifiedReduction X Z where
  reduction := first.reduction.comp second.reduction
  compiler := .comp first.compiler second.compiler
  mapWitness := fun F A W => second.mapWitness _ _ (first.mapWitness F A W)
  code_eq := by intros; rw [second.code_eq, first.code_eq]; rfl
  negligible := AdvantageBound.comp_preservesNegligible _ _ first.negligible second.negligible

theorem secure (T : CertifiedReduction X Y) (F) (h : Y.Secure (T.reduction.mapFamily F)) :
    X.Secure F := by
  apply T.reduction.secureOnWithin X.adversaries Y.adversaries F
  · exact ⟨T.toTransform.admissible⟩
  · exact T.negligible
  · exact h

end CertifiedReduction

structure CertifiedBinaryReduction {K : CodeSystem} {m n k : K.Machine}
    (X : SecurityObject.{u, v} K m) (Y : SecurityObject.{u, v} K n)
    (Z : SecurityObject.{u, v} K k) where
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

variable {K : CodeSystem} {m n k : K.Machine}
  {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n}
  {Z : SecurityObject.{u, v} K k}

theorem secure (T : CertifiedBinaryReduction X Y Z) (F)
    (hY : Y.Secure (T.left.transform.mapFamily F))
    (hZ : Z.Secure (T.right.transform.mapFamily F)) : X.Secure F := by
  intro A hA
  have hl := T.leftNegligible _ (hY _ (T.left.admissible F A hA))
  have hr := T.rightNegligible _ (hZ _ (T.right.admissible F A hA))
  exact Negligible.mono (T.advantage_le F A) (hl.add hr)

end CertifiedBinaryReduction
end CryptoLogic.General
