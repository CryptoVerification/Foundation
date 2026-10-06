import Foundation.Crypto.Logic.General.Execution
import Foundation.Crypto.Meta.MultiExtraction

/-! The existing hypothesis/transport/binary rules, with typed machine indices.
Execution models affect code and certificates, not the inference rules. -/
namespace CryptoLogic.General

universe u v a b

set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

/-- Only names, machine indices, and pure compiler syntax live here. -/
structure Language (K : CodeSystem) where
  Object : Type a
  machine : Object → K.Machine
  Unary : Object → Object → Type b
  unaryCompiler : ∀ {X Y}, Unary X Y → Compiler K (machine X) (machine Y)
  Binary : Object → Object → Object → Type b
  binaryCompilers : ∀ {X Y Z}, Binary X Y Z →
    Compiler K (machine X) (machine Y) × Compiler K (machine X) (machine Z)

structure Signature {K : CodeSystem} (L : Language.{a, b} K) where
  interpret : ∀ X, SecurityObject.{u, v} K (L.machine X)
  unary : ∀ {X Y}, L.Unary X Y → CertifiedReduction (interpret X) (interpret Y)
  unary_compiler : ∀ {X Y} (e : L.Unary X Y), (unary e).compiler = L.unaryCompiler e
  binary : ∀ {X Y Z}, L.Binary X Y Z → CertifiedBinaryReduction (interpret X) (interpret Y) (interpret Z)
  left_compiler : ∀ {X Y Z} (e : L.Binary X Y Z), (binary e).left.compiler = (L.binaryCompilers e).1
  right_compiler : ∀ {X Y Z} (e : L.Binary X Y Z), (binary e).right.compiler = (L.binaryCompilers e).2

inductive ReductionExpr {K : CodeSystem} (L : Language.{a, b} K) : L.Object → L.Object → Type (max a b) where
  | identity (X) : ReductionExpr L X X
  | primitive {X Y} : L.Unary X Y → ReductionExpr L X Y
  | seq {X Y Z} : ReductionExpr L X Y → ReductionExpr L Y Z → ReductionExpr L X Z

namespace ReductionExpr

variable {K : CodeSystem} {L : Language.{a, b} K}

def compiler {X Y} : ReductionExpr L X Y → Compiler K (L.machine X) (L.machine Y)
  | .identity X => .identity (L.machine X)
  | .primitive e => L.unaryCompiler e
  | .seq first second => .comp first.compiler second.compiler

def eval {X Y} (r : ReductionExpr L X Y) (S : Signature.{u, v} L) :
    CertifiedReduction (S.interpret X) (S.interpret Y) :=
  match r with
  | .identity X => CertifiedReduction.id (S.interpret X)
  | .primitive e => S.unary e
  | .seq first second => (first.eval S).comp (second.eval S)

theorem eval_compiler {X Y} (r : ReductionExpr L X Y) (S : Signature.{u, v} L) :
    (r.eval S).compiler = r.compiler := by
  induction r with
  | identity X => rfl
  | primitive e => exact S.unary_compiler e
  | seq first second hFirst hSecond =>
      change Compiler.comp (first.eval S).compiler (second.eval S).compiler = _
      rw [hFirst, hSecond]
      rfl

end ReductionExpr

/-- A pure plan. Hypotheses cache their machine index so running the plan
never evaluates the semantic context to discover an output code's type. -/
inductive Plan (K : CodeSystem) {length : Nat} (machines : Fin length → K.Machine) :
    K.Machine → Type where
  | hypothesis (i : Fin length) (m : K.Machine) (agrees : m = machines i) : Plan K machines m
  | unary {m n} : Compiler K m n → Plan K machines n → Plan K machines m
  | binary {m n k} : Compiler K m n → Compiler K m k →
      Plan K machines n → Plan K machines k → Plan K machines m

namespace Plan

variable {K : CodeSystem} {length targetLength : Nat}
  {machines : Fin length → K.Machine} {targets : Fin targetLength → K.Machine}

abbrev Output (K : CodeSystem) (length : Nat) := Fin length × (Sigma K.Code)
abbrev Path (K : CodeSystem) (length : Nat) (source : K.Machine) :=
  Fin length × (Sigma (Compiler K source))

def run {m} : Plan K machines m → K.Code m → List (Output K length)
  | .hypothesis i m _, code => [(i, ⟨m, code⟩)]
  | .unary c child, code => child.run (c.run code)
  | .binary c d left right, code => left.run (c.run code) ++ right.run (d.run code)

def paths {m} : Plan K machines m → List (Path K length m)
  | .hypothesis i m _ => [(i, ⟨m, .identity m⟩)]
  | .unary c child => child.paths.map fun (i, ⟨n, d⟩) => (i, ⟨n, .comp c d⟩)
  | .binary c d left right =>
      (left.paths.map fun (i, ⟨n, e⟩) => (i, ⟨n, .comp c e⟩)) ++
      (right.paths.map fun (i, ⟨n, e⟩) => (i, ⟨n, .comp d e⟩))

@[simp] theorem paths_unary {m n} (c : Compiler K m n) (child : Plan K machines n) :
    (Plan.unary c child).paths =
      child.paths.map (fun (i, ⟨n, d⟩) => (i, ⟨n, .comp c d⟩)) := rfl

@[simp] theorem paths_binary {m n k} (c : Compiler K m n) (d : Compiler K m k)
    (left : Plan K machines n) (right : Plan K machines k) :
    (Plan.binary c d left right).paths =
      (left.paths.map (fun (i, ⟨n, e⟩) => (i, ⟨n, .comp c e⟩))) ++
      (right.paths.map (fun (i, ⟨n, e⟩) => (i, ⟨n, .comp d e⟩))) := rfl

def first {m} : Plan K machines m → Fin length
  | .hypothesis i _ _ => i
  | .unary _ child => child.first
  | .binary _ _ left _ => left.first

/-- Every cached path generates exactly the recursively emitted code. -/
theorem paths_run {m} (plan : Plan K machines m) (code : K.Code m) :
    plan.paths.map (fun (i, ⟨n, c⟩) => (i, ⟨n, c.run code⟩)) = plan.run code := by
  induction plan with
  | hypothesis i m h => rfl
  | unary c child ih =>
      simp only [paths, run, List.map_map]
      exact ih (c.run code)
  | binary c d left right hl hr =>
      simp only [paths, run, List.map_append, List.map_map]
      exact congrArg₂ (· ++ ·) (hl (c.run code)) (hr (d.run code))

/-- Substitution respects the machine type of every replaced hypothesis. -/
def substitute {m} (plan : Plan K machines m)
    (replacement : ∀ i, Plan K targets (machines i)) : Plan K targets m :=
  match plan with
  | .hypothesis i m h => h.symm ▸ replacement i
  | .unary c child => .unary c (child.substitute replacement)
  | .binary c d left right => .binary c d (left.substitute replacement) (right.substitute replacement)

/-- Interpret replacement plans at the original leaves, preserving their
machine indices rather than casting an arbitrary packed output. -/
def runWith {m} (plan : Plan K machines m)
    (replacement : ∀ i, Plan K targets (machines i)) (code : K.Code m) : List (Output K targetLength) :=
  match plan with
  | .hypothesis i m h => (h.symm ▸ replacement i).run code
  | .unary c child => child.runWith replacement (c.run code)
  | .binary c d left right =>
      left.runWith replacement (c.run code) ++ right.runWith replacement (d.run code)

theorem run_substitute {m} (plan : Plan K machines m)
    (replacement : ∀ i, Plan K targets (machines i)) (code : K.Code m) :
    (plan.substitute replacement).run code = plan.runWith replacement code := by
  induction plan with
  | hypothesis i m h => rfl
  | unary c child ih => exact ih (c.run code)
  | binary c d left right hl hr => exact congrArg₂ (· ++ ·) (hl (c.run code)) (hr (d.run code))

end Plan

structure Claim {K : CodeSystem} {L : Language.{a, b} K} (S : Signature.{u, v} L) where
  object : L.Object
  family : InstanceFamily (S.interpret object).goal

/-- A finite context with direct bounded indexing, also accommodating the
legacy list contexts without casts in the semantic derivation rules. -/
structure Context {K : CodeSystem} {L : Language.{a, b} K} (S : Signature.{u, v} L) where
  length : Nat
  claim : Fin length → Claim S

namespace Context

variable {K : CodeSystem} {L : Language.{a, b} K} {S : Signature.{u, v} L}

@[macro_inline] def machines (Γ : Context S) : Fin Γ.length → K.Machine := fun i => L.machine (Γ.claim i).object

def Valid (Γ : Context S) : Prop := ∀ i, (S.interpret (Γ.claim i).object).Secure (Γ.claim i).family

end Context

inductive Tree {K : CodeSystem} {L : Language.{a, b} K} (S : Signature.{u, v} L) (Γ : Context S) :
    (X : L.Object) → InstanceFamily (S.interpret X).goal → Type (max u a b) where
  | hypothesis (i : Fin Γ.length) : Tree S Γ (Γ.claim i).object (Γ.claim i).family
  | transport {X Y} (r : ReductionExpr L X Y) (F)
      (child : Tree S Γ Y ((r.eval S).reduction.mapFamily F)) : Tree S Γ X F
  | binary {X Y Z} (e : L.Binary X Y Z) (F)
      (left : Tree S Γ Y ((S.binary e).left.transform.mapFamily F))
      (right : Tree S Γ Z ((S.binary e).right.transform.mapFamily F)) : Tree S Γ X F

namespace Tree

variable {K : CodeSystem} {L : Language.{a, b} K} {S : Signature.{u, v} L} {Γ Δ : Context S}

def plan {X F} : Tree S Γ X F → Plan K Γ.machines (L.machine X)
  | .hypothesis i => .hypothesis i (L.machine (Γ.claim i).object) rfl
  | .transport r _ child => .unary r.compiler child.plan
  | .binary e _ left right => .binary (L.binaryCompilers e).1 (L.binaryCompilers e).2 left.plan right.plan

def substitute {X F} (tree : Tree S Γ X F)
    (replacement : ∀ i, Tree S Δ (Γ.claim i).object (Γ.claim i).family) : Tree S Δ X F :=
  match tree with
  | .hypothesis i => replacement i
  | .transport r F child => .transport r F (child.substitute replacement)
  | .binary e F left right => .binary e F (left.substitute replacement) (right.substitute replacement)

theorem plan_substitute {X F} (tree : Tree S Γ X F)
    (replacement : ∀ i, Tree S Δ (Γ.claim i).object (Γ.claim i).family) :
    (tree.substitute replacement).plan = tree.plan.substitute (fun i => (replacement i).plan) := by
  induction tree with
  | hypothesis i => rfl
  | transport r F child ih => simp only [substitute, plan, Plan.substitute, ih]
  | binary e F left right hl hr => simp only [substitute, plan, Plan.substitute, hl, hr]

theorem sound {X F} (tree : Tree S Γ X F) (h : Γ.Valid) : (S.interpret X).Secure F := by
  induction tree with
  | hypothesis i => exact h i
  | transport r F child ih => exact (r.eval S).secure F ih
  | binary e F left right hl hr => exact (S.binary e).secure F hl hr

end Tree

/-- Only a pure plan and cached paths survive code generation. -/
structure Derivation {K : CodeSystem} {L : Language.{a, b} K} (S : Signature.{u, v} L)
    (Γ : Context S) (X : L.Object) (F : InstanceFamily (S.interpret X).goal) where
  plan : Plan K Γ.machines (L.machine X)
  compilers : List (Plan.Path K Γ.length (L.machine X))
  emitted_eq : ∀ code, compilers.map (fun (i, ⟨n, c⟩) => (i, ⟨n, c.run code⟩)) = plan.run code
  typed : ∃ tree : Tree S Γ X F, tree.plan = plan

namespace Derivation

variable {K : CodeSystem} {L : Language.{a, b} K} {S : Signature.{u, v} L} {Γ Δ : Context S}

@[macro_inline] def hypothesis (i : Fin Γ.length) :
    Derivation S Γ (Γ.claim i).object (Γ.claim i).family :=
  ⟨.hypothesis i (L.machine (Γ.claim i).object) rfl,
    [(i, ⟨L.machine (Γ.claim i).object, .identity _⟩)], fun _ => rfl, ⟨.hypothesis i, rfl⟩⟩

@[macro_inline] def transport {X Y} (r : ReductionExpr L X Y) (F)
    (child : Derivation S Γ Y ((r.eval S).reduction.mapFamily F)) : Derivation S Γ X F where
  plan := .unary r.compiler child.plan
  compilers := child.compilers.map fun (i, ⟨n, c⟩) => (i, ⟨n, .comp r.compiler c⟩)
  emitted_eq := by intro code; rw [List.map_map]; exact child.emitted_eq (r.compiler.run code)
  typed := by obtain ⟨tree, h⟩ := child.typed; exact ⟨.transport r F tree, congrArg _ h⟩

@[macro_inline] def binary {X Y Z} (e : L.Binary X Y Z) (F)
    (left : Derivation S Γ Y ((S.binary e).left.transform.mapFamily F))
    (right : Derivation S Γ Z ((S.binary e).right.transform.mapFamily F)) : Derivation S Γ X F where
  plan := .binary (L.binaryCompilers e).1 (L.binaryCompilers e).2 left.plan right.plan
  compilers :=
    (left.compilers.map fun (i, ⟨n, c⟩) => (i, ⟨n, .comp (L.binaryCompilers e).1 c⟩)) ++
    (right.compilers.map fun (i, ⟨n, c⟩) => (i, ⟨n, .comp (L.binaryCompilers e).2 c⟩))
  emitted_eq := by
    intro code
    rw [List.map_append, List.map_map, List.map_map]
    exact congrArg₂ (· ++ ·) (left.emitted_eq ((L.binaryCompilers e).1.run code))
      (right.emitted_eq ((L.binaryCompilers e).2.run code))
  typed := by
    obtain ⟨l, hl⟩ := left.typed
    obtain ⟨r, hr⟩ := right.typed
    exact ⟨.binary e F l r, by simp only [Tree.plan, hl, hr]⟩

@[macro_inline] def run {X F} (d : Derivation S Γ X F) (code : K.Code (L.machine X)) :
    List (Nat × Sigma K.Code) := d.compilers.map fun (i, ⟨n, c⟩) => (i.val, ⟨n, c.run code⟩)

noncomputable def checkedTree {X F} (d : Derivation S Γ X F) : Tree S Γ X F := Classical.choose d.typed

theorem checkedTree_plan {X F} (d : Derivation S Γ X F) : d.checkedTree.plan = d.plan :=
  Classical.choose_spec d.typed

theorem run_eq {X F} (d : Derivation S Γ X F) (code : K.Code (L.machine X)) :
    d.run code = (d.plan.run code).map (fun (i, packed) => (i.val, packed)) := by
  rw [← d.emitted_eq, List.map_map]
  rfl

theorem sound {X F} (d : Derivation S Γ X F) (h : Γ.Valid) : (S.interpret X).Secure F :=
  d.checkedTree.sound h

theorem no_empty {X F} (d : Derivation S Γ X F) (h : Γ.length = 0) : False := by
  have := d.plan.first.isLt
  omega

@[macro_inline] def substitute {X F} (d : Derivation S Γ X F)
    (replacement : ∀ i, Derivation S Δ (Γ.claim i).object (Γ.claim i).family) : Derivation S Δ X F where
  plan := d.plan.substitute (fun i => (replacement i).plan)
  compilers := (d.plan.substitute (fun i => (replacement i).plan)).paths
  emitted_eq := Plan.paths_run _
  typed := by
    classical
    obtain ⟨tree, h⟩ := d.typed
    choose trees ht using (fun i => (replacement i).typed)
    refine ⟨tree.substitute trees, ?_⟩
    rw [tree.plan_substitute, h]
    congr 1
    exact funext ht

end Derivation
end CryptoLogic.General
