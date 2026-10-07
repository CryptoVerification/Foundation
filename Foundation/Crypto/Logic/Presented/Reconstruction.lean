import Foundation.Crypto.Logic.Presented.Interpretation

/-! An exact reconstruction of every currently registered cryptographic tree.
Here the opaque public parameters are specialized to the existing family API.
This specialization is an instance of the presentation, not a dependency of
the general proof calculus. Both directions retain proof structure. -/
namespace CryptoLogic.Presented

open General
universe u v a b
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

variable {K : CodeSystem} {L : General.Language.{a, b} K}

def parameters (S : General.Signature.{u, v} L) : Parameters L where
  Family := fun X => InstanceFamily (S.interpret X).goal
  unary := fun r => (r.eval S).reduction.mapFamily
  left := fun e => (S.binary e).left.transform.mapFamily
  right := fun e => (S.binary e).right.transform.mapFamily

def interpretation (S : General.Signature.{u, v} L) : Interpretation (parameters S) S where
  family := fun F => F
  unary := by intros; rfl
  left := by intros; rfl
  right := by intros; rfl

def quoteContext {S : General.Signature.{u, v} L} (Γ : General.Context S) :
    Presented.Context (parameters S) where
  length := Γ.length
  claim i := ⟨(Γ.claim i).object, (Γ.claim i).family⟩

@[simp] theorem context_quote {S : General.Signature.{u, v} L} (Γ : General.Context S) :
    (interpretation S).context (quoteContext Γ) = Γ := rfl

def quote {S : General.Signature.{u, v} L} {Γ : General.Context S} {X F} :
    General.Tree S Γ X F → Presented.Derivation (parameters S) (quoteContext Γ) X F
  | .hypothesis i => Foundation.Logic.Derivation.hypothesis
      (T := presentation (parameters S)) (Γ := quoteContext Γ) i
  | .transport r F child => Presented.Derivation.transport r F (quote child)
  | .binary e F left right => Presented.Derivation.binary e F (quote left) (quote right)

theorem tree_quote {S : General.Signature.{u, v} L} {Γ : General.Context S} {X F}
    (t : General.Tree S Γ X F) : (interpretation S).tree (quote t) = t := by
  induction t with
  | hypothesis i => rfl
  | transport r F child ih => exact congrArg (General.Tree.transport r F) ih
  | binary e F left right hl hr => exact congrArg₂ (General.Tree.binary e F) hl hr

theorem quote_plan {S : General.Signature.{u, v} L} {Γ : General.Context S} {X F}
    (t : General.Tree S Γ X F) : Presented.Derivation.plan (quote t) = t.plan := by
  rw [← (interpretation S).tree_plan, tree_quote]

theorem quote_substitute {S : General.Signature.{u, v} L} {Γ Δ : General.Context S} {X F}
    (t : General.Tree S Γ X F)
    (replacement : ∀ i, General.Tree S Δ (Γ.claim i).object (Γ.claim i).family) :
    quote (t.substitute replacement) = (quote t).substitute (fun i => quote (replacement i)) := by
  induction t with
  | hypothesis i => rfl
  | transport r F child ih =>
      exact congrArg (Presented.Derivation.transport (P := parameters S) (Γ := quoteContext Δ) r F) ih
  | binary e F left right hl hr =>
      change Foundation.Logic.Derivation.apply (T := presentation (parameters S))
        (Γ := quoteContext Δ) (Rule.binary e F) _ =
        Foundation.Logic.Derivation.apply (T := presentation (parameters S))
          (Γ := quoteContext Δ) (Rule.binary e F) _
      apply congrArg (Foundation.Logic.Derivation.apply
        (T := presentation (parameters S)) (Γ := quoteContext Δ) (Rule.binary e F))
      funext i
      fin_cases i
      · exact hl
      · exact hr

theorem quote_tree {S : General.Signature.{u, v} L} {Γ : General.Context S}
    {A : Claim (parameters S)}
    (d : Foundation.Logic.Derivation (presentation (parameters S)) (quoteContext Γ) A) :
    quote ((interpretation S).tree d) = d := by
  refine Foundation.Logic.Derivation.rec
    (motive := fun A d => quote ((interpretation S).tree d) = d)
    (fun _ => rfl) (fun rule children ih => ?_) d
  cases rule with
  | transport r F =>
      change Foundation.Logic.Derivation.apply (T := presentation (parameters S))
        (Γ := quoteContext Γ) (Rule.transport r F)
        (fun _ => quote ((interpretation S).tree (children 0))) = _
      apply congrArg (Foundation.Logic.Derivation.apply
        (T := presentation (parameters S)) (Γ := quoteContext Γ) (Rule.transport r F))
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact ih 0
  | binary e F =>
      change Foundation.Logic.Derivation.apply (T := presentation (parameters S))
        (Γ := quoteContext Γ) (Rule.binary e F)
        (Fin.cases (motive := fun i => Foundation.Logic.Derivation
          (presentation (parameters S)) (quoteContext Γ)
          ((presentation (parameters S)).premise (Rule.binary e F) i))
          (quote ((interpretation S).tree (children 0)))
          (fun _ => quote ((interpretation S).tree (children 1)))) = _
      apply congrArg (Foundation.Logic.Derivation.apply
        (T := presentation (parameters S)) (Γ := quoteContext Γ) (Rule.binary e F))
      funext i
      fin_cases i
      · exact ih 0
      · exact ih 1

/-- Every existing certified derivation has a syntactic representative with
its exact compiler plan and output list, for every input code. -/
theorem reconstruct {S : General.Signature.{u, v} L} {Γ : General.Context S} {X F}
    (d : General.Derivation S Γ X F) :
    ∃ q : Presented.Derivation (parameters S) (quoteContext Γ) X F,
      Presented.Derivation.plan q = d.plan ∧
      ∀ code, Presented.Derivation.run q code = d.run code := by
  obtain ⟨t, ht⟩ := d.typed
  refine ⟨quote t, (quote_plan t).trans ht, ?_⟩
  intro code
  rw [General.Derivation.run_eq]
  change ((Presented.Derivation.plan (quote t)).run code).map _ = _
  rw [quote_plan, ht]
  rfl

/-- Completeness is relative to the existing registered inference trees. It
does not claim that every true security statement has a syntactic proof. -/
theorem derivable_iff {S : General.Signature.{u, v} L} {Γ : General.Context S} {X F} :
    Nonempty (Presented.Derivation (parameters S) (quoteContext Γ) X F) ↔
      Nonempty (General.Derivation S Γ X F) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨(interpretation S).legacy d⟩
  · rintro ⟨d⟩
    obtain ⟨t, _⟩ := d.typed
    exact ⟨quote t⟩

end CryptoLogic.Presented
