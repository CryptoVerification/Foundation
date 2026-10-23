import Foundation.Logic.Polygraph.Interpretation

/-! The free cartesian inference category. Equality is equality of formal
terms, not equality in one chosen security model. In particular distinct rule
symbols remain distinct. The quotient removes precisely the redundant diagram
notation; `forestEquiv` identifies its homs with families of free terms. -/
namespace Foundation.Logic.Polygraph

universe j r v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

variable {T : Presentation.{j, r}}

def structuralSetoid (T : Presentation.{j, r}) (Γ Δ : Logic.Context T) :
    Setoid (Diagram T Γ Δ) where
  r f g := f.toForest = g.toForest
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def Cell (T : Presentation.{j, r}) (Γ Δ : Logic.Context T) :=
  Quotient (structuralSetoid T Γ Δ)

namespace Cell

variable {Γ Δ Θ Ξ Γ' Δ' : Logic.Context T}

def ofDiagram (d : Diagram T Γ Δ) : Cell T Γ Δ := Quotient.mk _ d

def forest : Cell T Γ Δ → Forest Γ Δ :=
  Quotient.lift Diagram.toForest (fun _ _ h => h)

@[simp] theorem forest_ofDiagram (d : Diagram T Γ Δ) :
    forest (ofDiagram d) = d.toForest := rfl

theorem ofDiagram_eq_iff (f g : Diagram T Γ Δ) :
    ofDiagram f = ofDiagram g ↔ f.toForest = g.toForest := Quotient.eq

@[ext] theorem ext {f g : Cell T Γ Δ} (h : forest f = forest g) : f = g := by
  induction f using Quotient.inductionOn with | _ f =>
    induction g using Quotient.inductionOn with | _ g =>
      exact Quotient.sound h

def ofForest (f : Forest Γ Δ) : Cell T Γ Δ := ofDiagram (Diagram.ofForest f)

@[simp] theorem forest_ofForest (f : Forest Γ Δ) : forest (ofForest f) = f :=
  Diagram.toForest_ofForest f

@[simp] theorem ofForest_forest (f : Cell T Γ Δ) : ofForest (forest f) = f := by
  apply ext
  simp

def forestEquiv : Cell T Γ Δ ≃ Forest Γ Δ where
  toFun := forest
  invFun := ofForest
  left_inv := ofForest_forest
  right_inv := forest_ofForest

def identity (Γ : Logic.Context T) : Cell T Γ Γ := ofDiagram (.identity Γ)

def seq (f : Cell T Γ Δ) (g : Cell T Δ Θ) : Cell T Γ Θ :=
  ofForest (fun i => (forest g i).substitute (forest f))

@[simp] theorem forest_seq (f : Cell T Γ Δ) (g : Cell T Δ Θ) :
    forest (seq f g) = fun i => (forest g i).substitute (forest f) := forest_ofForest _

theorem seq_ofDiagram (f : Diagram T Γ Δ) (g : Diagram T Δ Θ) :
    seq (ofDiagram f) (ofDiagram g) = ofDiagram (.seq f g) := by
  apply ext
  simp [Diagram.toForest]

theorem seq_assoc (f : Cell T Γ Δ) (g : Cell T Δ Θ) (h : Cell T Θ Ξ) :
    seq (seq f g) h = seq f (seq g h) := by
  apply ext
  simp only [forest_seq]
  funext i
  exact (Logic.Derivation.substitute_assoc _ _ _).symm

@[simp] theorem identity_seq (f : Cell T Γ Δ) : seq (identity Γ) f = f := by
  apply ext
  simp only [forest_seq, identity, forest_ofDiagram, Diagram.toForest]
  funext i
  exact (forest f i).substitute_id

@[simp] theorem seq_identity (f : Cell T Γ Δ) : seq f (identity Δ) = f := by
  apply ext
  simp [identity, Diagram.toForest]

def tensor (f : Cell T Γ Δ) (g : Cell T Γ' Δ') :
    Cell T (Context.append Γ Γ') (Context.append Δ Δ') :=
  ofDiagram (.tensor (Diagram.ofForest (forest f)) (Diagram.ofForest (forest g)))

theorem tensor_ofDiagram (f : Diagram T Γ Δ) (g : Diagram T Γ' Δ') :
    tensor (ofDiagram f) (ofDiagram g) = ofDiagram (.tensor f g) := by
  apply ext
  simp [tensor, Diagram.toForest]

def tuple (f : ∀ i, Cell T Γ (Logic.Context.singleton (Δ.claim i))) : Cell T Γ Δ :=
  ofForest (fun i => forest (f i) 0)

def projection (Δ : Logic.Context T) (i : Fin Δ.length) :
    Cell T Δ (Logic.Context.singleton (Δ.claim i)) := ofDiagram (.wiring (.select Δ i))

@[simp] theorem tuple_projection (f : ∀ i, Cell T Γ (Logic.Context.singleton (Δ.claim i)))
    (i : Fin Δ.length) : seq (tuple f) (projection Δ i) = f i := by
  apply ext
  funext k
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  simp [tuple, projection, Diagram.toForest, Wiring.select]

@[simp] theorem tuple_eta (f : Cell T Γ Δ) :
    tuple (fun i => seq f (projection Δ i)) = f := by
  apply ext
  funext i
  simp [tuple, projection, Diagram.toForest, Wiring.select]

def eval (M : Model.{j, r, v} T) (f : Cell T Γ Δ) (env : Environment M Γ) :
    Environment M Δ := fun i => (forest f i).eval M env

@[simp] theorem eval_ofDiagram (M : Model.{j, r, v} T) (d : Diagram T Γ Δ)
    (env : Environment M Γ) : eval M (ofDiagram d) env = d.eval M env := by
  funext i
  exact Diagram.eval_toForest M d env i

theorem eval_seq (M : Model.{j, r, v} T) (f : Cell T Γ Δ) (g : Cell T Δ Θ)
    (env : Environment M Γ) : eval M (seq f g) env = eval M g (eval M f env) := by
  funext i
  simp only [eval, forest_seq]
  exact Logic.Derivation.eval_substitute M env _ _

theorem eval_tensor (M : Model.{j, r, v} T) (f : Cell T Γ Δ) (g : Cell T Γ' Δ')
    (env : Environment M (Context.append Γ Γ')) :
    eval M (tensor f g) env = Fin.addCases
      (fun k => (Context.append_left Δ Δ' k).symm ▸
        eval M f (fun i => Context.append_left Γ Γ' i ▸ env (Fin.castAdd Γ'.length i)) k)
      (fun k => (Context.append_right Δ Δ' k).symm ▸
        eval M g (fun i => Context.append_right Γ Γ' i ▸ env (Fin.natAdd Γ.length i)) k) := by
  simp only [tensor, eval_ofDiagram, Diagram.eval]
  have h : ∀ {A B : Logic.Context T} (f : Forest A B) (env : Environment M A),
      (Diagram.ofForest f).eval M env = fun i => (f i).eval M env := by
    intro A B f env
    funext i
    rw [← Diagram.eval_toForest, Diagram.toForest_ofForest]
  simp only [h, eval]

private theorem eval_term {A} (d : Logic.Derivation T Γ A) :
    d.eval (Model.termModel T Γ) (fun i => Logic.Derivation.hypothesis i) = d := by
  induction d with
  | hypothesis => rfl
  | apply rule children ih => exact congrArg (Logic.Derivation.apply rule) (funext ih)

/-- Equality is detected by the free term model, so the quotient does not
identify different cryptographic proofs merely because both are valid. -/
theorem eq_iff_all_models (f g : Cell T Γ Δ) : f = g ↔
    ∀ (M : Model.{j, r, max j r + 1} T) (env : Environment M Γ),
      eval M f env = eval M g env := by
  constructor
  · rintro rfl M env; rfl
  · intro h
    apply ext
    have ht := h (Model.termModel T Γ) (fun i => Logic.Derivation.hypothesis i)
    funext i
    simpa only [eval, eval_term] using congrFun ht i

@[simp] private theorem cast_roundtrip {J : Type j} (C : J → Sort v) {x y : J}
    (h : x = y) (z : C x) : (h.symm ▸ (h ▸ z : C y) : C x) = z := by
  cases h
  rfl

theorem tensor_identity (Γ Γ' : Logic.Context T) :
    tensor (identity Γ) (identity Γ') = identity (Context.append Γ Γ') := by
  apply (eq_iff_all_models _ _).mpr
  intro M env
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp [eval_tensor, identity, eval_ofDiagram, Diagram.eval]
  · intro k
    simp [eval_tensor, identity, eval_ofDiagram, Diagram.eval]

/-- Interchange: parallel composition is functorial for inference cells. -/
theorem tensor_seq {Θ' : Logic.Context T} (f : Cell T Γ Δ) (g : Cell T Δ Θ)
    (f' : Cell T Γ' Δ') (g' : Cell T Δ' Θ') :
    seq (tensor f f') (tensor g g') = tensor (seq f g) (seq f' g') := by
  apply (eq_iff_all_models _ _).mpr
  intro M env
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp only [eval_seq, eval_tensor, Fin.addCases_left]
    congr 2
    funext j
    simp only [cast_roundtrip]
  · intro k
    simp only [eval_seq, eval_tensor, Fin.addCases_right]
    congr 2
    funext j
    simp only [cast_roundtrip]

end Cell
end Foundation.Logic.Polygraph
