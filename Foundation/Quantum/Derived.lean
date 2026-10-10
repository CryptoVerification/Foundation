import Foundation.Quantum.Semantics

/-! The QKD round can be offered as a derived rule; expansion is an actual
Translation into the primitive equational presentation, with the standard
interpretation and substitution preservation theorems. -/
namespace Foundation.Quantum.Derived
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Rule where
  | base : Quantum.Rule → Rule
  | qkd {a b} : Term a b → Rule

abbrev presentation : Presentation where
  Judgment := Equation
  Rule := Rule
  arity := fun | .base r => Quantum.presentation.arity r | .qkd _ => 1
  premise := fun
    | .base r => Quantum.presentation.premise r
    | .qkd m => fun _ => equation (.seq (.dagger m) m) (.ident _)
  conclusion := fun
    | .base r => Quantum.presentation.conclusion r
    | .qkd m => equation (Term.alice m) (Term.bob m)

abbrev expansion : Translation presentation Quantum.presentation where
  judgment := id
  rule := fun r => match r with
    | .base r => Derivation.apply (T := Quantum.presentation) r
        (fun i => Derivation.hypothesis (T := Quantum.presentation)
          (Γ := (presentation.ruleContext (.base r)).map id) i)
    | .qkd m => Proof.qkd m (Derivation.hypothesis 0)

noncomputable abbrev model (σ : Assignment) : Model presentation :=
  expansion.pullback (Quantum.model σ)

theorem interpretation_expansion (σ : Assignment) {Γ : Context presentation}
    {E : Equation} (d : Derivation presentation Γ E)
    (h : ∀ i, (Γ.claim i).Valid σ) :
    (expansion.translate d).eval (Quantum.model σ) h = d.eval (model σ) h :=
  expansion.eval_translate _ h d

theorem expansion_substitute {Γ Δ : Context presentation} {E : Equation}
    (d : Derivation presentation Γ E)
    (replacement : ∀ i, Derivation presentation Δ (Γ.claim i)) :
    expansion.translate (d.substitute replacement) =
      (expansion.translate d).substitute (fun i => expansion.translate (replacement i)) :=
  expansion.translate_substitute d replacement

end Foundation.Quantum.Derived
