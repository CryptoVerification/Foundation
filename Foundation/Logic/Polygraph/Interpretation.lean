import Foundation.Logic.Polygraph.Presentation

/-! Direct compositional evaluation, independently of proof reconstruction.
Every existing rule model supplies an interpretation of logical diagrams. -/
namespace Foundation.Logic.Polygraph

universe j r v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

abbrev Environment {T : Presentation.{j, r}} (M : Model.{j, r, v} T)
    (Γ : Logic.Context T) := ∀ i, M.Carrier (Γ.claim i)

namespace Diagram

variable {T : Presentation.{j, r}}

def eval (M : Model.{j, r, v} T) : {Γ Δ : Logic.Context T} →
    Diagram T Γ Δ → Environment M Γ → Environment M Δ
  | _, _, .identity _, env => env
  | _, _, .generator rule, env => fun _ => M.operation rule env
  | _, _, .wiring w, env => fun i => w.agrees i ▸ env (w.index i)
  | _, _, .seq first second, env => eval M second (eval M first env)
  | _, _, .tensor (Γ := Γ) (Δ := Δ) (Γ' := Γ') (Δ' := Δ') first second, env =>
      Fin.addCases
        (fun k => (Context.append_left Δ Δ' k).symm ▸
          eval M first (fun i => Context.append_left Γ Γ' i ▸ env (Fin.castAdd Γ'.length i)) k)
        (fun k => (Context.append_right Δ Δ' k).symm ▸
          eval M second (fun i => Context.append_right Γ Γ' i ▸ env (Fin.natAdd Γ.length i)) k)
  | _, _, .tuple children, env => fun i => eval M (children i) env 0

private theorem eval_cast {Γ : Logic.Context T} {A B : T.Judgment}
    (h : A = B) (d : Logic.Derivation T Γ A) (M : Model.{j, r, v} T)
    (env : Environment M Γ) :
    (h ▸ d : Logic.Derivation T Γ B).eval M env = h ▸ d.eval M env := by
  cases h
  rfl

/-- Direct evaluation agrees with evaluation of each reconstructed tree. -/
theorem eval_toForest (M : Model.{j, r, v} T) {Γ Δ : Logic.Context T}
    (d : Diagram T Γ Δ) (env : Environment M Γ) (i : Fin Δ.length) :
    (toForest d i).eval M env = eval M d env i := by
  induction d with
  | identity => rfl
  | generator rule => rfl
  | wiring w => exact eval_cast (w.agrees i) _ M env
  | seq first second ihFirst ihSecond =>
      rw [toForest, Logic.Derivation.eval_substitute]
      rw [show (fun k => (toForest first k).eval M env) = eval M first env from
        funext (fun k => ihFirst env k)]
      exact ihSecond _ i
  | tensor first second ihFirst ihSecond =>
      refine Fin.addCases ?_ ?_ i
      · intro k
        simp only [toForest, eval, Fin.addCases_left, eval_cast,
          Logic.Derivation.rename, Logic.Derivation.eval_substitute]
        simp only [Logic.Derivation.eval]
        rw [ihFirst]
      · intro k
        simp only [toForest, eval, Fin.addCases_right, eval_cast,
          Logic.Derivation.rename, Logic.Derivation.eval_substitute]
        simp only [Logic.Derivation.eval]
        rw [ihSecond]
  | tuple children ih => exact ih i env 0

@[simp] theorem eval_ofDerivation (M : Model.{j, r, v} T)
    {Γ : Logic.Context T} {A} (d : Logic.Derivation T Γ A)
    (env : Environment M Γ) (i : Fin 1) :
    eval M (ofDerivation d) env i = d.eval M env := by
  rw [← eval_toForest, toForest_ofDerivation]

end Diagram
end Foundation.Logic.Polygraph
