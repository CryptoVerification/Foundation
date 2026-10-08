import Mathlib.Data.Fin.Basic

/-! A free, proof-relevant calculus of finite-arity inference rules. Neither
judgments nor rules are required to denote propositions, programs, or security
experiments. A context is a finite indexed family, retaining repeated uses.
This is a rule presentation, not an implementation of arbitrary dependent GATs.
-/
namespace Foundation.Logic

universe j r v w

set_option linter.checkUnivs false

structure Presentation where
  Judgment : Type j
  Rule : Type r
  arity : Rule → Nat
  premise : (rule : Rule) → Fin (arity rule) → Judgment
  conclusion : Rule → Judgment

structure Context (T : Presentation.{j, r}) where
  length : Nat
  claim : Fin length → T.Judgment

namespace Context

abbrev empty (T : Presentation.{j, r}) : Context T := ⟨0, Fin.elim0⟩
abbrev singleton {T : Presentation.{j, r}} (A : T.Judgment) : Context T := ⟨1, fun _ => A⟩

end Context

inductive Derivation (T : Presentation.{j, r}) (Γ : Context T) :
    T.Judgment → Type (max j r) where
  | hypothesis (i : Fin Γ.length) : Derivation T Γ (Γ.claim i)
  | apply (rule : T.Rule)
      (children : ∀ i, Derivation T Γ (T.premise rule i)) :
      Derivation T Γ (T.conclusion rule)

namespace Derivation

variable {T : Presentation.{j, r}} {Γ Δ Θ : Context T}

def substitute {A} (d : Derivation T Γ A)
    (replacement : ∀ i, Derivation T Δ (Γ.claim i)) : Derivation T Δ A :=
  match d with
  | .hypothesis i => replacement i
  | .apply rule children => .apply rule (fun i => (children i).substitute replacement)

@[simp] theorem substitute_hypothesis (i : Fin Γ.length)
    (replacement : ∀ i, Derivation T Δ (Γ.claim i)) :
    (hypothesis i : Derivation T Γ (Γ.claim i)).substitute replacement = replacement i := rfl

@[simp] theorem substitute_apply (rule : T.Rule)
    (children : ∀ i, Derivation T Γ (T.premise rule i))
    (replacement : ∀ i, Derivation T Δ (Γ.claim i)) :
    (apply rule children : Derivation T Γ (T.conclusion rule)).substitute replacement =
      apply rule (fun i => (children i).substitute replacement) := rfl

@[simp] theorem substitute_id {A} (d : Derivation T Γ A) :
    d.substitute (fun i => hypothesis i) = d := by
  induction d with
  | hypothesis i => rfl
  | apply rule children ih =>
      simp only [substitute]
      exact congrArg (apply rule) (funext ih)

theorem substitute_assoc {A} (d : Derivation T Γ A)
    (first : ∀ i, Derivation T Δ (Γ.claim i))
    (second : ∀ i, Derivation T Θ (Δ.claim i)) :
    (d.substitute first).substitute second =
      d.substitute (fun i => (first i).substitute second) := by
  induction d with
  | hypothesis i => rfl
  | apply rule children ih =>
      simp only [substitute]
      exact congrArg (apply rule) (funext ih)

/-- Renaming retains the judgment at each original position. It may forget,
reorder, or duplicate positions; this is logical reuse, not reuse of keys. -/
def rename {A} (d : Derivation T Γ A) (index : Fin Γ.length → Fin Δ.length)
    (agrees : ∀ i, Δ.claim (index i) = Γ.claim i) : Derivation T Δ A :=
  d.substitute (fun i => agrees i ▸ hypothesis (index i))

end Derivation

/-- A proof-relevant interpretation. Sort-valued carriers also allow ordinary
truth-valued semantics; no executable interpretation is required. -/
structure Model (T : Presentation.{j, r}) where
  Carrier : T.Judgment → Sort v
  operation : (rule : T.Rule) →
    (∀ i, Carrier (T.premise rule i)) → Carrier (T.conclusion rule)

namespace Derivation

variable {T : Presentation.{j, r}} {Γ Δ : Context T}

def eval (M : Model.{j, r, v} T) (hypotheses : ∀ i, M.Carrier (Γ.claim i)) :
    {A : T.Judgment} → Derivation T Γ A → M.Carrier A
  | _, .hypothesis i => hypotheses i
  | _, .apply rule children => M.operation rule (fun i => (children i).eval M hypotheses)

/-- Interpretation commutes with cut; the right side interprets replacement
proofs once as the environment for the original proof. -/
theorem eval_substitute (M : Model.{j, r, v} T) (hypotheses : ∀ i, M.Carrier (Δ.claim i))
    {A} (d : Derivation T Γ A) (replacement : ∀ i, Derivation T Δ (Γ.claim i)) :
    (d.substitute replacement).eval M hypotheses =
      d.eval M (fun i => (replacement i).eval M hypotheses) := by
  induction d with
  | hypothesis i => rfl
  | apply rule children ih =>
      simp only [substitute, eval]
      exact congrArg (M.operation rule) (funext ih)

end Derivation

namespace Model

variable {T : Presentation.{j, r}}

structure Hom (M : Model.{j, r, v} T) (N : Model.{j, r, w} T) where
  map : ∀ A, M.Carrier A → N.Carrier A
  preserves : ∀ rule children,
    map _ (M.operation rule children) = N.operation rule (fun i => map _ (children i))

def termModel (T : Presentation.{j, r}) (Γ : Context T) : Model T where
  Carrier := Derivation T Γ
  operation := Derivation.apply

def interpretation {Γ : Context T} (M : Model.{j, r, v} T)
    (hypotheses : ∀ i, M.Carrier (Γ.claim i)) : Hom (termModel T Γ) M where
  map := fun _ d => d.eval M hypotheses
  preserves := by intros; rfl

/-- The free model on the context: uniqueness is of the entire proof-relevant
interpretation, not just of the final proposition's truth value. -/
theorem interpretation_unique {Γ : Context T} (M : Model.{j, r, v} T)
    (hypotheses : ∀ i, M.Carrier (Γ.claim i))
    (f : Hom (termModel T Γ) M)
    (h : ∀ i, f.map _ (.hypothesis i) = hypotheses i) :
    f = interpretation M hypotheses := by
  have maps : ∀ A (d : Derivation T Γ A), f.map A d = d.eval M hypotheses := by
    intro A d
    induction d with
    | hypothesis i => exact h i
    | apply rule children ih =>
        exact (f.preserves rule children).trans (congrArg (M.operation rule) (funext ih))
  cases f with
  | mk map preserves =>
      have hm : map = (interpretation M hypotheses).map := funext (fun A => funext (maps A))
      cases hm
      rfl

/-- With no hypotheses the term model is initial. Nullary rules may produce
closed proofs; their validity must be supplied by each model. -/
theorem initial (T : Presentation.{j, r}) (M : Model.{j, r, v} T) :
    ∃! _f : Hom (termModel T (Context.empty T)) M, True := by
  refine ⟨interpretation M (fun i => Fin.elim0 i), trivial, ?_⟩
  intro f _
  exact interpretation_unique M _ f (fun i => Fin.elim0 i)

theorem eval_hom {Γ : Context T} {M : Model.{j, r, v} T} {N : Model.{j, r, w} T}
    (f : Hom M N) (hypotheses : ∀ i, M.Carrier (Γ.claim i))
    {A} (d : Derivation T Γ A) :
    f.map _ (d.eval M hypotheses) = d.eval N (fun i => f.map _ (hypotheses i)) := by
  induction d with
  | hypothesis i => rfl
  | apply rule children ih =>
      rw [Derivation.eval, f.preserves]
      exact congrArg (N.operation rule) (funext ih)

end Model
end Foundation.Logic
