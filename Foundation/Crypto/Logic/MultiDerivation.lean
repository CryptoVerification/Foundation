import Foundation.Crypto.Meta.Soundness
import Foundation.Crypto.Semantics.Machine.BinaryReduction

namespace CryptoLogic

universe u v w a b

set_option linter.checkUnivs false in
structure MultiLanguage where
  unary : Language.{a, b}
  Binary : unary.Object → unary.Object → unary.Object → Type b
  compilers : ∀ {X Y Z}, Binary X Y Z → Machine.ProgramCompiler × Machine.ProgramCompiler

set_option linter.checkUnivs false in
structure MultiSignature (L : MultiLanguage.{a, b}) where
  unary : Signature.{u, v, w} L.unary
  binary : ∀ {X Y Z}, L.Binary X Y Z →
    CertifiedBinaryReduction (unary.interpret X) (unary.interpret Y) (unary.interpret Z)
  left_compiler : ∀ {X Y Z} (e : L.Binary X Y Z), (binary e).left.compiler = (L.compilers e).1
  right_compiler : ∀ {X Y Z} (e : L.Binary X Y Z), (binary e).right.compiler = (L.compilers e).2

/-- Pure finite code-generation tree; repeated context positions remain distinct leaves. -/
inductive CompilerTree (length : Nat) where
  | hypothesis (index : Fin length)
  | unary (compiler : Machine.ProgramCompiler) (child : CompilerTree length)
  | binary (left right : Machine.ProgramCompiler) (l r : CompilerTree length)

namespace CompilerTree

def ofUnary {L : Language.{a, b}} {length} : DerivationSyntax L length → CompilerTree length
  | .hypothesis i => .hypothesis i
  | .transport r t => .unary r.compiler (ofUnary t)

def paths {length} : CompilerTree length → List (Fin length × Machine.ProgramCompiler)
  | .hypothesis i => [(i, .identity)]
  | .unary c t => t.paths.map fun (i, k) => (i, .comp c k)
  | .binary c d l r =>
    (l.paths.map fun (i, k) => (i, .comp c k)) ++
      (r.paths.map fun (i, k) => (i, .comp d k))

def first {length} : CompilerTree length → Fin length
  | .hypothesis i => i
  | .unary _ t => t.first
  | .binary _ _ l _ => l.first

def run {length} (t : CompilerTree length) (p : Machine.Program) :
    List (Fin length × Machine.Program) := t.paths.map fun (i, c) => (i, c.run p)

def substitute {length targetLength} : CompilerTree length →
    (Fin length → CompilerTree targetLength) → CompilerTree targetLength
  | .hypothesis i, f => f i
  | .unary c t, f => .unary c (t.substitute f)
  | .binary c d l r, f => .binary c d (l.substitute f) (r.substitute f)

theorem run_unary {length} (c) (t : CompilerTree length) (p) :
    (unary c t).run p = t.run (c.run p) := by
  simp [run, paths, List.map_map, Function.comp_def, Machine.ProgramCompiler.run]

theorem run_binary {length} (c d) (l r : CompilerTree length) (p) :
    (binary c d l r).run p = l.run (c.run p) ++ r.run (d.run p) := by
  simp [run, paths, List.map_map, Function.comp_def, Machine.ProgramCompiler.run]

theorem run_ofUnary {L : Language.{a, b}} {length} (t : DerivationSyntax L length) (p) :
    (ofUnary t).run p = [(t.selected, t.compiler.run p)] := by
  induction t generalizing p with
  | hypothesis i => rfl
  | transport r t ih =>
    simpa only [ofUnary, run_unary, DerivationSyntax.selected, DerivationSyntax.compiler,
      Machine.ProgramCompiler.run] using ih (r.compiler.run p)

theorem run_substitute {length targetLength} (t : CompilerTree length)
    (f : Fin length → CompilerTree targetLength) (p) :
    (t.substitute f).run p = (t.run p).flatMap fun (i, q) => (f i).run q := by
  induction t generalizing p with
  | hypothesis i => simp [substitute, run, paths, Machine.ProgramCompiler.run]
  | unary c t ih => simp only [substitute, run_unary]; exact ih _
  | binary c d l r hl hr => simp [substitute, run_binary, hl, hr]

end CompilerTree

variable {L : MultiLanguage.{a, b}} {S : MultiSignature.{u, v, w} L}

inductive MultiTree (S : MultiSignature.{u, v, w} L) (Γ : Context S.unary) :
    (X : L.unary.Object) → InstanceFamily (S.unary.interpret X).goal → Type (max u a b) where
  | hypothesis (i : Fin Γ.length) : MultiTree S Γ (Γ[i]).object (Γ[i]).family
  | transport {X Y} (r : ReductionExpr L.unary X Y) (F)
      (child : MultiTree S Γ Y ((r.eval S.unary).reduction.mapFamily F)) : MultiTree S Γ X F
  | binary {X Y Z} (e : L.Binary X Y Z) (F)
      (left : MultiTree S Γ Y ((S.binary e).left.transform.mapFamily F))
      (right : MultiTree S Γ Z ((S.binary e).right.transform.mapFamily F)) : MultiTree S Γ X F

namespace MultiTree

variable {Γ Δ : Context S.unary}

def plan {X F} : MultiTree S Γ X F → CompilerTree Γ.length
  | .hypothesis i => .hypothesis i
  | .transport r _ child => .unary r.compiler child.plan
  | .binary e _ l r => .binary (L.compilers e).1 (L.compilers e).2 l.plan r.plan

def ofUnary {X F} : DerivationTree S.unary Γ X F → MultiTree S Γ X F
  | .hypothesis i => .hypothesis i
  | .transport r F child => .transport r F (ofUnary child)

theorem ofUnary_plan {X F} (t : DerivationTree S.unary Γ X F) :
    (MultiTree.ofUnary t).plan = CompilerTree.ofUnary t.code := by
  induction t with
  | hypothesis i => rfl
  | transport r F t ih => simp [ofUnary, plan, CompilerTree.ofUnary, DerivationTree.code, ih]

def substitute {X F} (t : MultiTree S Γ X F)
    (f : ∀ i : Fin Γ.length, MultiTree S Δ (Γ[i]).object (Γ[i]).family) : MultiTree S Δ X F :=
  match t with
  | .hypothesis i => f i
  | .transport r F child => .transport r F (child.substitute f)
  | .binary e F l r => .binary e F (l.substitute f) (r.substitute f)

theorem plan_substitute {X F} (t : MultiTree S Γ X F)
    (f : ∀ i : Fin Γ.length, MultiTree S Δ (Γ[i]).object (Γ[i]).family) :
    (t.substitute f).plan = t.plan.substitute (fun i => (f i).plan) := by
  induction t with
  | hypothesis i => rfl
  | transport r F child ih => simp [substitute, plan, CompilerTree.substitute, ih]
  | binary e F l r hl hr => simp [substitute, plan, CompilerTree.substitute, hl, hr]

theorem sound {X F} (t : MultiTree S Γ X F) (hΓ : Γ.Valid) :
    (S.unary.interpret X).Secure F := by
  induction t with
  | hypothesis i => exact hΓ i
  | transport r F child ih => exact (r.eval S.unary).secure F ih
  | binary e F l r hl hr => exact (S.binary e).secure F hl hr

end MultiTree

/-- Executable plan and erased semantic evidence, as in the unary fragment. -/
structure MultiDerivation (S : MultiSignature.{u, v, w} L) (Γ : Context S.unary)
    (X : L.unary.Object) (F : InstanceFamily (S.unary.interpret X).goal) where
  plan : CompilerTree Γ.length
  compilers : List (Fin Γ.length × Machine.ProgramCompiler)
  emitted_eq : ∀ p, compilers.map (fun (i, c) => (i, c.run p)) = plan.run p
  typed : ∃ t : MultiTree S Γ X F, t.plan = plan

namespace MultiDerivation

variable {Γ Δ : Context S.unary}

@[macro_inline] def hypothesis (i : Fin Γ.length) :
    MultiDerivation S Γ (Γ[i]).object (Γ[i]).family :=
  ⟨.hypothesis i, [(i, .identity)], fun _ => rfl, ⟨.hypothesis i, rfl⟩⟩

@[macro_inline] def transport {X Y} (r : ReductionExpr L.unary X Y) (F)
    (child : MultiDerivation S Γ Y ((r.eval S.unary).reduction.mapFamily F)) :
    MultiDerivation S Γ X F where
  plan := .unary r.compiler child.plan
  compilers := child.compilers.map fun (i, c) => (i, .comp r.compiler c)
  emitted_eq := by
    intro p
    rw [CompilerTree.run_unary, List.map_map]
    simpa only [Function.comp_def, Machine.ProgramCompiler.run] using
      child.emitted_eq (r.compiler.run p)
  typed := by obtain ⟨t, h⟩ := child.typed; exact ⟨.transport r F t, congrArg _ h⟩

@[macro_inline] def binary {X Y Z} (e : L.Binary X Y Z) (F)
    (left : MultiDerivation S Γ Y ((S.binary e).left.transform.mapFamily F))
    (right : MultiDerivation S Γ Z ((S.binary e).right.transform.mapFamily F)) :
    MultiDerivation S Γ X F where
  plan := .binary (L.compilers e).1 (L.compilers e).2 left.plan right.plan
  compilers := (left.compilers.map fun (i, c) => (i, .comp (L.compilers e).1 c)) ++
    (right.compilers.map fun (i, c) => (i, .comp (L.compilers e).2 c))
  emitted_eq := by
    intro p
    rw [CompilerTree.run_binary, List.map_append, List.map_map, List.map_map]
    simpa only [Function.comp_def, Machine.ProgramCompiler.run] using
      congrArg₂ (fun xs ys : List (Fin Γ.length × Machine.Program) => xs ++ ys)
        (left.emitted_eq ((L.compilers e).1.run p))
        (right.emitted_eq ((L.compilers e).2.run p))
  typed := by
    obtain ⟨l, hl⟩ := left.typed
    obtain ⟨r, hr⟩ := right.typed
    exact ⟨.binary e F l r, by simp only [MultiTree.plan, hl, hr]⟩

@[macro_inline] def ofUnary {X F} (d : Derivation S.unary Γ X F) : MultiDerivation S Γ X F where
  plan := CompilerTree.ofUnary d.code
  compilers := [(d.code.selected, d.compiler)]
  emitted_eq := by intro p; simp only [List.map_cons, List.map_nil, CompilerTree.run_ofUnary]; rw [d.compiler_eq]
  typed := by
    obtain ⟨t, h⟩ := d.typed
    exact ⟨MultiTree.ofUnary t, by rw [MultiTree.ofUnary_plan, h]⟩

theorem ofUnary_run {X F} (d : Derivation S.unary Γ X F) (p) :
    (MultiDerivation.ofUnary d).plan.run p = [(d.code.selected, d.compiler.run p)] := by
  rw [ofUnary, CompilerTree.run_ofUnary, ← d.compiler_eq]

/-- Run cached pure compilers without evaluating the semantic context length. -/
@[macro_inline] def run {X F} (d : MultiDerivation S Γ X F) (p : Machine.Program) :
    List (Nat × Machine.Program) := d.compilers.map fun (i, c) => (i.val, c.run p)

theorem run_eq {X F} (d : MultiDerivation S Γ X F) (p : Machine.Program) :
    d.run p = (d.plan.run p).map (fun (i, q) => (i.val, q)) := by
  rw [← d.emitted_eq p, List.map_map]
  rfl

noncomputable def checkedTree {X F} (d : MultiDerivation S Γ X F) : MultiTree S Γ X F :=
  Classical.choose d.typed

theorem checkedTree_plan {X F} (d : MultiDerivation S Γ X F) : d.checkedTree.plan = d.plan :=
  Classical.choose_spec d.typed

theorem sound {X F} (d : MultiDerivation S Γ X F) (hΓ : Γ.Valid) :
    (S.unary.interpret X).Secure F := d.checkedTree.sound hΓ

theorem no_empty {X F} (d : MultiDerivation S [] X F) : False := Fin.elim0 d.plan.first

end MultiDerivation
end CryptoLogic
