import Foundation.Logic.Presentation

/-! A translation maps judgments to judgments and each inference rule to an
entire target derivation from the translated premises. It therefore supports
derived rules, including rules with zero or more than two premises. -/
namespace Foundation.Logic

universe j r k s l q v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace Context

abbrev map {T : Presentation.{j, r}} {U : Presentation.{k, s}}
    (Γ : Context T) (f : T.Judgment → U.Judgment) : Context U where
  length := Γ.length
  claim := fun i => f (Γ.claim i)

end Context

namespace Presentation

abbrev ruleContext (T : Presentation.{j, r}) (rule : T.Rule) : Context T where
  length := T.arity rule
  claim := T.premise rule

end Presentation

structure Translation (T : Presentation.{j, r}) (U : Presentation.{k, s}) where
  judgment : T.Judgment → U.Judgment
  rule : ∀ r, Derivation U ((T.ruleContext r).map judgment) (judgment (T.conclusion r))

namespace Translation

variable {T : Presentation.{j, r}} {U : Presentation.{k, s}} {V : Presentation.{l, q}}

def translate (f : Translation T U) {Γ : Context T} :
    {A : T.Judgment} → Derivation T Γ A → Derivation U (Γ.map f.judgment) (f.judgment A)
  | _, .hypothesis i => Derivation.hypothesis (T := U) (Γ := Γ.map f.judgment) i
  | _, .apply rule children => (f.rule rule).substitute (fun i => f.translate (children i))

@[simp] theorem translate_hypothesis (f : Translation T U) {Γ : Context T} (i : Fin Γ.length) :
    f.translate (Derivation.hypothesis i : Derivation T Γ (Γ.claim i)) =
      Derivation.hypothesis (T := U) (Γ := Γ.map f.judgment) i := rfl

theorem translate_substitute (f : Translation T U) {Γ Δ : Context T} {A}
    (d : Derivation T Γ A) (replacement : ∀ i, Derivation T Δ (Γ.claim i)) :
    f.translate (d.substitute replacement) =
      (f.translate d).substitute (fun i => f.translate (replacement i)) := by
  induction d with
  | hypothesis i => rfl
  | apply rule children ih =>
      simp only [Derivation.substitute, translate, Derivation.substitute_assoc]
      exact congrArg ((f.rule rule).substitute) (funext ih)

abbrev identity (T : Presentation.{j, r}) : Translation T T where
  judgment := id
  rule := fun r => Derivation.apply (T := T) (Γ := (T.ruleContext r).map id) r
    (fun i => Derivation.hypothesis (T := T) (Γ := (T.ruleContext r).map id) i)

@[simp] theorem translate_identity {Γ : Context T} {A} (d : Derivation T Γ A) :
    (identity T).translate d = d := by
  induction d with
  | hypothesis i => rfl
  | apply rule children ih =>
      change Derivation.apply rule (fun i => (identity T).translate (children i)) = _
      exact congrArg (Derivation.apply rule) (funext ih)

abbrev comp (first : Translation T U) (second : Translation U V) : Translation T V where
  judgment := fun A => second.judgment (first.judgment A)
  rule := fun r => second.translate (first.rule r)

/-- Translating a whole proof by a composite expands rules in the same order
as translating the proof twice. -/
theorem translate_comp (first : Translation T U) (second : Translation U V)
    {Γ : Context T} {A} (d : Derivation T Γ A) :
    (first.comp second).translate d = second.translate (first.translate d) := by
  induction d with
  | hypothesis i => rfl
  | apply rule children ih =>
      change (second.translate (first.rule rule)).substitute
        (fun i => (first.comp second).translate (children i)) =
          second.translate ((first.rule rule).substitute (fun i => first.translate (children i)))
      rw [second.translate_substitute]
      exact congrArg ((second.translate (first.rule rule)).substitute) (funext ih)

@[simp] theorem comp_identity (f : Translation T U) : f.comp (identity U) = f := by
  cases f with
  | mk judgment rule =>
      change Translation.mk judgment _ = Translation.mk judgment rule
      apply congrArg (Translation.mk judgment)
      funext r
      exact translate_identity (rule r)

@[simp] theorem identity_comp (f : Translation T U) : (identity T).comp f = f := by
  cases f with
  | mk judgment rule =>
      change Translation.mk judgment _ = Translation.mk judgment rule
      apply congrArg (Translation.mk judgment)
      funext r
      exact (rule r).substitute_id

theorem comp_assoc {W : Presentation} (f : Translation T U) (g : Translation U V)
    (h : Translation V W) : (f.comp g).comp h = f.comp (g.comp h) := by
  cases f with
  | mk judgment rule =>
      change Translation.mk (fun A => h.judgment (g.judgment (judgment A))) _ =
        Translation.mk (fun A => h.judgment (g.judgment (judgment A))) _
      apply congrArg (Translation.mk (fun A => h.judgment (g.judgment (judgment A))))
      funext r
      exact (translate_comp g h (rule r)).symm

/-- Target models interpret derived rules, inducing a source model without
requiring a separate semantic certificate for each expanded proof. -/
abbrev pullback (f : Translation T U) (M : Model.{k, s, v} U) : Model T where
  Carrier := fun A => M.Carrier (f.judgment A)
  operation := fun r children => (f.rule r).eval M children

/-- The interpretation square commutes for every model, including models
whose values retain proof trees, code, or analysis data. -/
theorem eval_translate (f : Translation T U) (M : Model.{k, s, v} U)
    {Γ : Context T} (environment : ∀ i, M.Carrier (f.judgment (Γ.claim i)))
    {A} (d : Derivation T Γ A) :
    (f.translate d).eval M environment = d.eval (f.pullback M) environment := by
  induction d with
  | hypothesis i => rfl
  | apply rule children ih =>
      change ((f.rule rule).substitute (fun i => f.translate (children i))).eval M environment = _
      rw [Derivation.eval_substitute]
      exact congrArg
        (fun hs : ∀ i, M.Carrier (f.judgment (T.premise rule i)) => (f.rule rule).eval M hs)
        (funext ih)

/-- A caller specifies which semantic data must survive translation by a
homomorphism into the pulled-back target model. Preservation of arbitrary
unrelated source and target models is not assumed. -/
theorem eval_preserving (f : Translation T U) {M : Model T} {N : Model U}
    (preservation : Model.Hom M (f.pullback N)) {Γ : Context T}
    (environment : ∀ i, M.Carrier (Γ.claim i)) {A} (d : Derivation T Γ A) :
    Derivation.eval (Γ := Γ.map f.judgment) N
      (fun i => preservation.map _ (environment i)) (f.translate d) =
      preservation.map _ (d.eval M environment) := by
  rw [f.eval_translate]
  exact (Model.eval_hom preservation environment d).symm

end Translation
end Foundation.Logic
