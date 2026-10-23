import Foundation.Logic.Polygraph.Structural

/-! Rule expansion between presentations, together with explicit structural
paths for composition, substitution, identity, and composed translations. -/
namespace Foundation.Logic.Polygraph

universe j r k s l q v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace Translation
variable {T : Presentation.{j, r}} {U : Presentation.{k, s}} {V : Presentation.{l, q}}

def diagram (f : Logic.Translation T U) {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) :
    Diagram U (Γ.map f.judgment) (Δ.map f.judgment) :=
  Diagram.ofForest (fun i => f.translate (d.toForest i))

@[simp] theorem forest_diagram (f : Logic.Translation T U) {Γ Δ : Logic.Context T}
    (d : Diagram T Γ Δ) : (diagram f d).toForest = fun i => f.translate (d.toForest i) :=
  Diagram.toForest_ofForest _

def seqPath (f : Logic.Translation T U) {Γ Δ Θ : Logic.Context T}
    (d : Diagram T Γ Δ) (e : Diagram T Δ Θ) :
    Diagram.Cell3 (diagram f (.seq d e)) (.seq (diagram f d) (diagram f e)) :=
  Diagram.connect _ _ (by
    simp only [forest_diagram, Diagram.toForest]
    funext i
    exact f.translate_substitute _ _)

def identityPath {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) :
    Diagram.Cell3 (diagram (Logic.Translation.identity T) d) d :=
  Diagram.connect _ _ (by simp [forest_diagram])

def compPath (f : Logic.Translation T U) (g : Logic.Translation U V)
    {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) :
    Diagram.Cell3 (diagram (f.comp g) d) (diagram g (diagram f d)) :=
  Diagram.connect _ _ (by
    simp only [forest_diagram]
    funext i
    exact Logic.Translation.translate_comp f g _)

def substitutePath (f : Logic.Translation T U) {Γ Δ Θ : Logic.Context T}
    (d : Diagram T Γ Θ) (replacement : Forest Δ Γ) :
    Diagram.Cell3 (diagram f (d.substitute replacement))
      ((diagram f d).substitute (fun i => f.translate (replacement i))) :=
  Diagram.connect _ _ (by
    funext i
    simp only [forest_diagram, Diagram.toForest_substitute]
    exact f.translate_substitute _ _)

theorem eval_diagram (f : Logic.Translation T U) (M : Model.{k, s, v} U)
    {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ)
    (env : Environment (f.pullback M) Γ) (i : Fin Δ.length) :
    (diagram f d).eval M env i = d.eval (f.pullback M) env i := by
  rw [← Diagram.eval_toForest, forest_diagram, f.eval_translate,
    Diagram.eval_toForest]

theorem eval_preserving (f : Logic.Translation T U) {M : Model T} {N : Model U}
    (preservation : Model.Hom M (f.pullback N)) {Γ Δ : Logic.Context T}
    (d : Diagram T Γ Δ) (env : Environment M Γ) (i : Fin Δ.length) :
    (diagram f d).eval N (fun k => preservation.map _ (env k)) i =
      preservation.map _ (d.eval M env i) := by
  rw [← Diagram.eval_toForest, forest_diagram,
    f.eval_preserving preservation env, Diagram.eval_toForest]

end Translation
end Foundation.Logic.Polygraph
