import Foundation.Logic.Polygraph.CartesianCoherence

/-! Explicit cartesian structural paths. Copying and deletion act on logical
assumptions; they do not copy randomness, machine states, or executions.
Every path below can be compared by Cartesian.coherent. -/
namespace Foundation.Logic.Polygraph
universe j r v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
variable {T : Presentation.{j, r}}

namespace Wiring

def duplicate (Γ : Logic.Context T) : Wiring Γ (Context.append Γ Γ) where
  index := Fin.addCases (m := Γ.length) (n := Γ.length) (fun i => i) (fun i => i)
  agrees := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simp only [Fin.addCases_left]
    · intro k
      simp only [Fin.addCases_right]

def comp {Γ Δ Θ : Logic.Context T} (w : Wiring Γ Δ) (v : Wiring Δ Θ) : Wiring Γ Θ :=
  ⟨fun i => w.index (v.index i), fun i => (w.agrees (v.index i)).trans (v.agrees i)⟩

end Wiring
namespace Cartesian
variable {Γ Δ Θ Ξ Γ' Δ' Θ' : Logic.Context T}

private theorem cast_roundtrip {J : Type j} (C : J → Sort v) {x y : J}
    (h : x = y) (z : C x) : (h ▸ (h.symm ▸ z : C y) : C x) = z := by
  cases h
  rfl

private theorem cast_comp {J : Type j} (C : J → Sort v) {x y z : J}
    (h : x = y) (k : y = z) (a : C x) :
    (k ▸ (h ▸ a : C y) : C z) = (h.trans k) ▸ a := by
  cases h
  cases k
  rfl

private theorem forest_of_eval {f g : Diagram T Γ Δ}
    (h : ∀ (M : Model.{j, r, (max j r) + 1} T) (env : Environment M Γ),
      f.eval M env = g.eval M env) : f.toForest = g.toForest :=
  (Cell.ofDiagram_eq_iff f g).mp ((Cell.eq_iff_all_models _ _).mpr (by
    intro M env
    simpa only [Cell.eval_ofDiagram] using h M env))

def interchange (f : Diagram T Γ Δ) (g : Diagram T Δ Θ)
    (f' : Diagram T Γ' Δ') (g' : Diagram T Δ' Θ') :
    Diagram.Cell3 (.seq (.tensor f f') (.tensor g g')) (.tensor (.seq f g) (.seq f' g')) :=
  Diagram.connect _ _ ((Cell.ofDiagram_eq_iff _ _).mp
    (by
      simpa only [Cell.seq_ofDiagram, Cell.tensor_ofDiagram] using
        (Cell.tensor_seq (Cell.ofDiagram f) (Cell.ofDiagram g) (Cell.ofDiagram f') (Cell.ofDiagram g'))))

private theorem cast_index {I : Type} {J : Type j} (C : J → Sort v)
    (A : I → J) (f : ∀ i, C (A i)) {i k : I} {B : J}
    (e : i = k) (h : A i = B) (h' : A k = B) : (h ▸ f i : C B) = h' ▸ f k := by
  cases e
  rfl

theorem eval_duplicate (Γ : Logic.Context T) (M : Model.{j, r, v} T) (env : Environment M Γ) :
    (Diagram.wiring (Wiring.duplicate Γ)).eval M env =
      Fin.addCases (fun i => (Context.append_left Γ Γ i).symm ▸ env i)
        (fun i => (Context.append_right Γ Γ i).symm ▸ env i) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp only [Diagram.eval, Fin.addCases_left]
    exact cast_index M.Carrier Γ.claim env (by simp [Wiring.duplicate]) _ _
  · intro k
    simp only [Diagram.eval, Fin.addCases_right]
    exact cast_index M.Carrier Γ.claim env (by simp only [Wiring.duplicate, Fin.addCases_right]) _ _

theorem duplicate_forest (d : Diagram T Γ Δ) :
    (Diagram.seq d (.wiring (Wiring.duplicate Δ))).toForest =
      (Diagram.seq (.wiring (Wiring.duplicate Γ)) (.tensor d d)).toForest := by
  apply forest_of_eval
  intro M env
  change (Diagram.wiring (Wiring.duplicate Δ)).eval M (d.eval M env) =
    (Diagram.tensor d d).eval M ((Diagram.wiring (Wiring.duplicate Γ)).eval M env)
  rw [eval_duplicate, eval_duplicate]
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp only [Diagram.eval, Fin.addCases_left]
    congr 2
    funext i
    simp only [Fin.addCases_left, cast_roundtrip]
  · intro k
    simp only [Diagram.eval, Fin.addCases_right]
    congr 2
    funext i
    simp only [Fin.addCases_right, cast_roundtrip]

def duplicateNatural (d : Diagram T Γ Δ) :
    Diagram.Cell3 (.seq d (.wiring (Wiring.duplicate Δ)))
      (.seq (.wiring (Wiring.duplicate Γ)) (.tensor d d)) :=
  Diagram.connect _ _ (duplicate_forest d)

def discardNatural (d : Diagram T Γ Δ) :
    Diagram.Cell3 (.seq d (.wiring (Wiring.discard Δ))) (.wiring (Wiring.discard Γ)) :=
  Diagram.connect _ _ (funext fun i => Fin.elim0 i)

def wiringComp (w : Wiring Γ Δ) (v : Wiring Δ Θ) :
    Diagram.Cell3 (.seq (.wiring w) (.wiring v)) (.wiring (w.comp v)) :=
  Diagram.connect _ _ (forest_of_eval fun M env => by
    funext i
    exact cast_comp M.Carrier (w.agrees (v.index i)) (v.agrees i) (env (w.index (v.index i))))

def tupleProjection (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i)))
    (i : Fin Δ.length) :
    Diagram.Cell3 (.seq (.tuple children) (.wiring (Wiring.select Δ i))) (children i) :=
  Diagram.connect _ _ (by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    simp [Diagram.toForest, Wiring.select])

def tupleEta (d : Diagram T Γ Δ) :
    Diagram.Cell3 (.tuple (fun i => .seq d (.wiring (Wiring.select Δ i)))) d :=
  Diagram.connect _ _ (by funext i; simp [Diagram.toForest, Wiring.select])

end Cartesian
end Foundation.Logic.Polygraph
