import Foundation.Crypto.Logic.General.Backends
import Foundation.Crypto.Meta.General.Extraction

/-! The old API embeds into the common execution-model kernel. Its exact
instance families, security classes, source code, and resource certificates
are retained. Legacy callers need not change their declarations. -/
namespace CryptoLogic.General.Legacy

open Backends

universe u v w a b

set_option backward.isDefEq.respectTransparency false

variable {L : CryptoLogic.MultiLanguage.{a, b}}

def language (L : CryptoLogic.MultiLanguage.{a, b}) : General.Language.{a, max a b} system where
  Object := L.unary.Object
  machine := fun _ => .native
  Unary := CryptoLogic.ReductionExpr L.unary
  unaryCompiler := fun e => .primitive (.native e.compiler)
  Binary := fun X Y Z => ULift.{max a b} (L.Binary X Y Z)
  binaryCompilers := fun e =>
    (.primitive (.native (L.compilers e.down).1), .primitive (.native (L.compilers e.down).2))

def signature (S : CryptoLogic.MultiSignature.{u, v, w} L) : General.Signature (language L) where
  interpret := fun X => nativeObject (S.unary.interpret X)
  unary := fun e => Native.reduction (e.eval S.unary)
  unary_compiler := by intro X Y e; simp only [Native.reduction, language]; rw [e.eval_compiler S.unary]
  binary := fun e => Native.binary (S.binary e.down)
  left_compiler := by intro X Y Z e; simp only [Native.binary, Native.transform, language]; rw [S.left_compiler e.down]
  right_compiler := by intro X Y Z e; simp only [Native.binary, Native.transform, language]; rw [S.right_compiler e.down]

@[macro_inline] def context {S : CryptoLogic.MultiSignature.{u, v, w} L} (Γ : CryptoLogic.Context S.unary) :
    General.Context (signature S) where
  length := Γ.length
  claim := fun i => ⟨(Γ[i]).object, (Γ[i]).family⟩

/-- Preserve the old context's exact finite positions and assertions. -/
theorem context_valid {S : CryptoLogic.MultiSignature.{u, v, w} L}
    (Γ : CryptoLogic.Context S.unary) : (context Γ).Valid ↔ Γ.Valid := Iff.rfl

def expression {X Y} (r : CryptoLogic.ReductionExpr L.unary X Y) :
    General.ReductionExpr (language L) X Y := .primitive r

theorem expression_reduction {S : CryptoLogic.MultiSignature.{u, v, w} L} {X Y}
    (r : CryptoLogic.ReductionExpr L.unary X Y) :
    ((expression r).eval (signature S)).reduction = (r.eval S.unary).reduction := rfl

theorem expression_run {X Y} (r : CryptoLogic.ReductionExpr L.unary X Y) (code : Machine.Program) :
    (expression r).compiler.run code = r.compiler.run code := rfl

/-- Conversion of semantic trees permits use of the same generalized
soundness and extraction kernel for every previously registered reduction. -/
def tree {S : CryptoLogic.MultiSignature.{u, v, w} L} {Γ : CryptoLogic.Context S.unary} {X F} :
    CryptoLogic.MultiTree S Γ X F → General.Tree (signature S) (context Γ) X F
  | .hypothesis i => General.Tree.hypothesis (S := signature S) (Γ := context Γ) i
  | .transport r F child =>
      General.Tree.transport (S := signature S) (Γ := context Γ) (expression r) F (tree child)
  | .binary e F left right =>
      General.Tree.binary (S := signature S) (Γ := context Γ) (ULift.up e) F (tree left) (tree right)

/-- Pure legacy compiler plans also translate without a semantic signature. -/
def plan {length} : CryptoLogic.CompilerTree length →
    General.Plan system (fun _ : Fin length => Kind.native) Kind.native
  | .hypothesis i => General.Plan.hypothesis (K := system)
      (machines := fun _ : Fin length => Kind.native) i Kind.native rfl
  | .unary c child => .unary (.primitive (Primitive.native c)) (plan child)
  | .binary c d left right => .binary (.primitive (Primitive.native c)) (.primitive (Primitive.native d)) (plan left) (plan right)

theorem plan_run {length} (p : CryptoLogic.CompilerTree length) (code : Machine.Program) :
    (plan p).run code = (p.run code).map (fun (i, output) => (i, ⟨Kind.native, output⟩)) := by
  induction p generalizing code with
  | hypothesis i => rfl
  | unary c child ih =>
      rw [CryptoLogic.CompilerTree.run_unary]
      exact ih (c.run code)
  | binary c d left right hl hr =>
      rw [CryptoLogic.CompilerTree.run_binary, List.map_append]
      exact congrArg₂ (· ++ ·) (hl (c.run code)) (hr (d.run code))

theorem tree_plan {S : CryptoLogic.MultiSignature.{u, v, w} L} {Γ : CryptoLogic.Context S.unary} {X F}
    (t : CryptoLogic.MultiTree S Γ X F) : (tree t).plan = plan t.plan := by
  induction t with
  | hypothesis i => rfl
  | transport r F child ih =>
      change Plan.unary _ (tree child).plan = Plan.unary _ (plan child.plan)
      rw [ih]
      rfl
  | binary e F left right hl hr =>
      change Plan.binary _ _ (tree left).plan (tree right).plan =
        Plan.binary _ _ (plan left.plan) (plan right.plan)
      rw [hl, hr]
      rfl

@[macro_inline] def derivation {S : CryptoLogic.MultiSignature.{u, v, w} L}
    {Γ : CryptoLogic.Context S.unary} {X F} (d : CryptoLogic.MultiDerivation S Γ X F) :
    General.Derivation (signature S) (context Γ) X F where
  plan := plan d.plan
  compilers := (plan d.plan).paths
  emitted_eq := Plan.paths_run _
  typed := by
    obtain ⟨t, h⟩ := d.typed
    exact ⟨tree t, by rw [tree_plan, h]⟩

theorem derivation_run {S : CryptoLogic.MultiSignature.{u, v, w} L}
    {Γ : CryptoLogic.Context S.unary} {X F} (d : CryptoLogic.MultiDerivation S Γ X F)
    (code : Machine.Program) :
    (derivation d).run code = (d.run code).map (fun (i, output) => (i, ⟨Kind.native, output⟩)) := by
  rw [General.Derivation.run_eq, CryptoLogic.MultiDerivation.run_eq]
  change ((plan d.plan).run code).map _ = _
  rw [plan_run, List.map_map, List.map_map]
  rfl

/-- Correspondence is about actual emitted code, not merely both security
conclusions being true. -/
theorem tree_run {S : CryptoLogic.MultiSignature.{u, v, w} L} {Γ : CryptoLogic.Context S.unary} {X F}
    (t : CryptoLogic.MultiTree S Γ X F) (code : Machine.Program) :
    (tree t).plan.run code = (t.plan.run code).map (fun (i, output) => (i, ⟨Kind.native, output⟩)) := by
  rw [tree_plan]
  exact plan_run t.plan code

theorem tree_loss {S : CryptoLogic.MultiSignature.{u, v, w} L} {Γ : CryptoLogic.Context S.unary} {X F}
    (t : CryptoLogic.MultiTree S Γ X F) : (tree t).loss = t.loss := by
  induction t with
  | hypothesis i => rfl
  | transport r F child ih =>
      change CryptoLogic.LossTree.unary ((expression r).eval (signature S)).reduction.loss (tree child).loss = _
      rw [expression_reduction, ih]
      rfl
  | binary e F left right hl hr =>
      change CryptoLogic.LossTree.binary _ _ (tree left).loss (tree right).loss = _
      rw [hl, hr]
      rfl

namespace Unary

def language (L : CryptoLogic.Language.{a, b}) : CryptoLogic.MultiLanguage where
  unary := L
  Binary := fun _ _ _ => PEmpty
  compilers := fun e => nomatch e

def signature {L : CryptoLogic.Language.{a, b}} (S : CryptoLogic.Signature.{u, v, w} L) :
    CryptoLogic.MultiSignature (language L) where
  unary := S
  binary := fun e => nomatch e
  left_compiler := fun e => nomatch e
  right_compiler := fun e => nomatch e

@[macro_inline] def derivation {L : CryptoLogic.Language.{a, b}}
    {S : CryptoLogic.Signature.{u, v, w} L} {Γ : CryptoLogic.Context S} {X F}
    (d : CryptoLogic.Derivation S Γ X F) :
    General.Derivation (Legacy.signature (signature S)) (Legacy.context Γ) X F :=
  Legacy.derivation (CryptoLogic.MultiDerivation.ofUnary (S := signature S) d)

theorem derivation_run {L : CryptoLogic.Language.{a, b}}
    {S : CryptoLogic.Signature.{u, v, w} L} {Γ : CryptoLogic.Context S} {X F}
    (d : CryptoLogic.Derivation S Γ X F) (code : Machine.Program) :
    (derivation d).run code = [(d.code.selected.val, ⟨Kind.native, d.compiler.run code⟩)] := by
  have h := Legacy.derivation_run (S := signature S)
    (CryptoLogic.MultiDerivation.ofUnary (S := signature S) d) code
  rw [CryptoLogic.MultiDerivation.run_eq, CryptoLogic.MultiDerivation.ofUnary_run] at h
  exact h


end Unary
end CryptoLogic.General.Legacy
