import Foundation.Logic.Polygraph.Basic

/-! Diagrams interpret as ordered families of existing proof trees. The
interpretation retains repeated hypothesis occurrences and all rule nodes. -/
namespace Foundation.Logic.Polygraph

universe j r
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

abbrev Forest {T : Presentation.{j, r}} (Γ Δ : Logic.Context T) :=
  ∀ i, Logic.Derivation T Γ (Δ.claim i)

namespace Diagram

variable {T : Presentation.{j, r}}

def toForest : {Γ Δ : Logic.Context T} → Diagram T Γ Δ → Forest Γ Δ
  | _, _, .identity _ => fun i => .hypothesis i
  | _, _, .generator rule => fun _ => .apply rule
      (fun i => Logic.Derivation.hypothesis (T := T) (Γ := T.ruleContext rule) i)
  | _, _, .wiring w => fun i => w.agrees i ▸ Logic.Derivation.hypothesis (w.index i)
  | _, _, .seq first second => fun i => (toForest second i).substitute (toForest first)
  | _, _, .tensor (Γ := Γ) (Δ := Δ) (Γ' := Γ') (Δ' := Δ') first second =>
      Fin.addCases
        (fun i => (Context.append_left Δ Δ' i).symm ▸
          (toForest first i).rename (Δ := Context.append Γ Γ') (Fin.castAdd Γ'.length)
            (Context.append_left Γ Γ'))
        (fun i => (Context.append_right Δ Δ' i).symm ▸
          (toForest second i).rename (Δ := Context.append Γ Γ') (Fin.natAdd Γ.length)
            (Context.append_right Γ Γ'))
  | _, _, .tuple children => fun i => toForest (children i) 0

def ofDerivation {Γ : Logic.Context T} {A} (d : Logic.Derivation T Γ A) :
    Diagram T Γ (Logic.Context.singleton A) :=
  match d with
  | .hypothesis i => .wiring (Wiring.select Γ i)
  | .apply rule children =>
      .seq (.tuple (fun i => ofDerivation (children i))) (.generator rule)

def ofForest {Γ Δ : Logic.Context T} (f : Forest Γ Δ) : Diagram T Γ Δ :=
  .tuple (fun i => ofDerivation (f i))

@[simp] theorem toForest_ofDerivation {Γ : Logic.Context T} {A}
    (d : Logic.Derivation T Γ A) (i : Fin 1) :
    toForest (ofDerivation d) i = d := by
  induction d generalizing i with
  | hypothesis i => rfl
  | apply rule children ih =>
      change Logic.Derivation.apply rule
        (fun k => toForest (ofDerivation (children k)) 0) = _
      exact congrArg (Logic.Derivation.apply rule) (funext (fun k => ih k 0))

@[simp] theorem toForest_ofForest {Γ Δ : Logic.Context T} (f : Forest Γ Δ) :
    toForest (ofForest f) = f := by
  funext i
  exact toForest_ofDerivation (f i) 0

/-- One output selects the unique reconstructed proof, without any model. -/
def toDerivation {Γ : Logic.Context T} {A}
    (d : Diagram T Γ (Logic.Context.singleton A)) : Logic.Derivation T Γ A :=
  toForest d 0

@[simp] theorem toDerivation_ofDerivation {Γ : Logic.Context T} {A}
    (d : Logic.Derivation T Γ A) : toDerivation (ofDerivation d) = d :=
  toForest_ofDerivation d 0

/-- Cut is explicit sequential composition with a reconstructed forest. -/
def substitute {Γ Δ Θ : Logic.Context T} (d : Diagram T Γ Θ)
    (replacement : Forest Δ Γ) : Diagram T Δ Θ :=
  .seq (ofForest replacement) d

@[simp] theorem toForest_substitute {Γ Δ Θ : Logic.Context T} (d : Diagram T Γ Θ)
    (replacement : Forest Δ Γ) (i : Fin Θ.length) :
    toForest (substitute d replacement) i = (toForest d i).substitute replacement := by
  simp only [substitute, toForest, toForest_ofDerivation, ofForest]

theorem toForest_seq_assoc {Γ Δ Θ Ξ : Logic.Context T}
    (f : Diagram T Γ Δ) (g : Diagram T Δ Θ) (h : Diagram T Θ Ξ) :
    toForest (.seq (.seq f g) h) = toForest (.seq f (.seq g h)) := by
  funext i
  exact (Logic.Derivation.substitute_assoc (toForest h i) (toForest g) (toForest f)).symm

@[simp] theorem toForest_seq_identity {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) :
    toForest (.seq d (.identity Δ)) = toForest d := rfl

@[simp] theorem toForest_identity_seq {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ) :
    toForest (.seq (.identity Γ) d) = toForest d := by
  funext i
  exact (toForest d i).substitute_id

end Diagram
end Foundation.Logic.Polygraph
