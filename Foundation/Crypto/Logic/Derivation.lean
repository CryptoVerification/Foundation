import Foundation.Crypto.Logic.Reduction

namespace CryptoLogic

universe u v w a b

variable {L : Language.{a, b}}

/-- A security assertion includes the precise instance family. -/
structure Claim (S : Signature.{u, v, w} L) where
  object : L.Object
  family : InstanceFamily (S.interpret object).goal

abbrev Context (S : Signature.{u, v, w} L) := List (Claim S)

/-- The two security rules. Hypotheses refer to positions in a finite context.
Transport requires security on exactly the reduction's mapped family. There
is no rule introducing semantic truth, or an unregistered reduction. -/
inductive DerivationTree (S : Signature.{u, v, w} L) (Γ : Context S) :
    (X : L.Object) → InstanceFamily (S.interpret X).goal → Type (max u a b) where
  | hypothesis (i : Fin Γ.length) : DerivationTree S Γ (Γ[i]).object (Γ[i]).family
  | transport {X Y} (r : ReductionExpr L X Y)
      (F : InstanceFamily (S.interpret X).goal)
      (premise : DerivationTree S Γ Y ((r.eval S).reduction.mapFamily F)) :
      DerivationTree S Γ X F

namespace DerivationTree

variable {S : Signature.{u, v, w} L} {Γ Δ : Context S}

/-- The compiler is computed from syntax alone, independently of the truth of
any security hypothesis or the chosen instance family. -/
def compiler {X F} (d : DerivationTree S Γ X F) : Machine.ProgramCompiler :=
  let rec go {X F} : DerivationTree S Γ X F → Machine.ProgramCompiler
    | .hypothesis _ => .identity
    | .transport r _ premise => .comp r.compiler (go premise)
  go d

/-- Substitute a derivation for each security assumption. This is the cut
operation for the unary fragment; it is structural and preserves typing of
the exact instance families. -/
def substitute {X F} (d : DerivationTree S Γ X F)
    (replacement : ∀ i : Fin Γ.length,
      DerivationTree S Δ (Γ[i]).object (Γ[i]).family) : DerivationTree S Δ X F :=
  let rec go {X F} : DerivationTree S Γ X F → DerivationTree S Δ X F
    | .hypothesis i => replacement i
    | .transport r F premise => .transport r F (go premise)
  go d

end DerivationTree

/-- Executable proof syntax. Context positions are bounded, but no semantic
signature or instance-family function is stored in this tree. -/
inductive DerivationSyntax (L : Language.{a, b}) (length : Nat) : Type (max a b) where
  | hypothesis (i : Fin length)
  | transport {X Y} (r : ReductionExpr L X Y) (premise : DerivationSyntax L length)

namespace DerivationSyntax

def compiler {length} : DerivationSyntax L length → Machine.ProgramCompiler
  | .hypothesis _ => .identity
  | .transport r premise => .comp r.compiler premise.compiler

def selected {length} : DerivationSyntax L length → Fin length
  | .hypothesis i => i
  | .transport _ premise => premise.selected

def substitute {length targetLength} (d : DerivationSyntax L length)
    (replacement : Fin length → DerivationSyntax L targetLength) : DerivationSyntax L targetLength :=
  match d with
  | .hypothesis i => replacement i
  | .transport r premise => .transport r (premise.substitute replacement)

theorem selected_substitute {length targetLength} (d : DerivationSyntax L length)
    (replacement : Fin length → DerivationSyntax L targetLength) :
    (d.substitute replacement).selected = (replacement d.selected).selected := by
  induction d with
  | hypothesis i => rfl
  | transport r premise ih => exact ih

theorem substitute_congr {length targetLength} (d : DerivationSyntax L length)
    (r s : Fin length → DerivationSyntax L targetLength) (h : ∀ i, r i = s i) :
    d.substitute r = d.substitute s := by
  congr 1
  exact funext h

end DerivationSyntax

namespace DerivationTree

variable {S : Signature.{u, v, w} L} {Γ Δ : Context S}

def code {X F} : DerivationTree S Γ X F → DerivationSyntax L Γ.length
  | .hypothesis i => .hypothesis i
  | .transport r _ premise => .transport r premise.code

theorem code_compiler {X F} (d : DerivationTree S Γ X F) :
    d.code.compiler = d.compiler := by
  induction d with
  | hypothesis i => rfl
  | transport r F premise ih =>
      change Machine.ProgramCompiler.comp r.compiler premise.code.compiler =
        Machine.ProgramCompiler.comp r.compiler premise.compiler
      rw [ih]

theorem code_substitute {X F} (d : DerivationTree S Γ X F)
    (replacement : ∀ i : Fin Γ.length,
      DerivationTree S Δ (Γ[i]).object (Γ[i]).family) :
    (d.substitute replacement).code = d.code.substitute (fun i => (replacement i).code) := by
  induction d with
  | hypothesis i => rfl
  | transport r F premise ih =>
      change DerivationSyntax.transport r (premise.substitute replacement).code =
        DerivationSyntax.transport r (premise.code.substitute (fun i => (replacement i).code))
      rw [ih]

end DerivationTree

/-- Pure executable syntax and cached compiler, with proof-only typing and
compiler-agreement certificates. Semantic derivation trees are inside `Prop`
and erased during code generation. Storing the compiler also avoids passing a
noncomputable semantic signature to recursive code-generation functions. -/
structure Derivation (S : Signature.{u, v, w} L) (Γ : Context S)
    (X : L.Object) (F : InstanceFamily (S.interpret X).goal) where
  code : DerivationSyntax L Γ.length
  compiler : Machine.ProgramCompiler
  compiler_eq : compiler = code.compiler
  typed : ∃ tree : DerivationTree S Γ X F, tree.code = code

namespace Derivation

variable {S : Signature.{u, v, w} L} {Γ Δ : Context S}

/-- Expand before code generation so semantic arguments used only in types
and proofs are erased, even when the signature is noncomputable. Ordinary
`inline` runs too late to provide this guarantee. -/
@[macro_inline] def hypothesis (i : Fin Γ.length) : Derivation S Γ (Γ[i]).object (Γ[i]).family :=
  ⟨.hypothesis i, .identity, rfl, ⟨.hypothesis i, rfl⟩⟩

@[macro_inline] def transport {X Y} (r : ReductionExpr L X Y)
    (F : InstanceFamily (S.interpret X).goal)
    (premise : Derivation S Γ Y ((r.eval S).reduction.mapFamily F)) :
    Derivation S Γ X F where
  code := .transport r premise.code
  compiler := .comp r.compiler premise.compiler
  compiler_eq := by
    change Machine.ProgramCompiler.comp r.compiler premise.compiler =
      Machine.ProgramCompiler.comp r.compiler premise.code.compiler
    rw [premise.compiler_eq]
  typed := by
    obtain ⟨tree, h⟩ := premise.typed
    exact ⟨.transport r F tree, congrArg (DerivationSyntax.transport r) h⟩

@[macro_inline] def substitute {X F} (d : Derivation S Γ X F)
    (replacement : ∀ i : Fin Γ.length,
      Derivation S Δ (Γ[i]).object (Γ[i]).family) : Derivation S Δ X F where
  code := d.code.substitute (fun i => (replacement i).code)
  compiler := (d.code.substitute (fun i => (replacement i).code)).compiler
  compiler_eq := rfl
  typed := by
    classical
    obtain ⟨tree, h⟩ := d.typed
    choose trees hTrees using (fun i => (replacement i).typed)
    refine ⟨tree.substitute trees, ?_⟩
    rw [tree.code_substitute, h]
    exact d.code.substitute_congr _ _ hTrees

end Derivation
end CryptoLogic
