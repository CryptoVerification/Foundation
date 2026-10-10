import Foundation.Quantum.Semantics
import Foundation.Quantum.Structures
import Foundation.Quantum.Derived
import Foundation.Quantum.Hilbert

/-! A closed derivation, its nontrivial complex matrix interpretation, and a
counterexample to copying an unknown state by the classical copy map. -/
namespace Foundation.Quantum.Examples
open Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Variable gates are unused by the closed example; no measurement equation
is required of this assignment. In particular it is not an all-unitary model. -/
def zeros : Assignment := fun _ _ _ => 0

/-- The selected gate really creates two nonzero amplitudes. -/
theorem mix_superposition : Op.mix 0 0 ≠ 0 ∧ Op.mix 1 0 ≠ 0 := by
  norm_num [Op.mix, Space.Basis, Space.basisDecidableEq, Complex.ext_iff]

/-- A one-rule use of the protocol expands to the primitive object logic. -/
def macroMix : Derivation Derived.presentation (Context.empty Derived.presentation)
    (equation (Term.alice .mix) (Term.bob .mix)) :=
  Derivation.apply (T := Derived.presentation) (Derived.Rule.qkd .mix) (fun _ =>
    Derivation.apply (T := Derived.presentation) (Derived.Rule.base (.law .mixEpi))
      (fun i => Fin.elim0 i))

def expandedMix := Derived.expansion.translate macroMix

theorem expanded_mix_correct : (Term.alice .mix).eval zeros = (Term.bob .mix).eval zeros :=
  sound zeros expandedMix (fun i => Fin.elim0 i)

/-- The result follows from evaluating the closed meta-logic derivation. -/
theorem qkd_mix : (Term.alice .mix).eval zeros = (Term.bob .mix).eval zeros :=
  sound zeros qkdMix (fun i => Fin.elim0 i)

/-- The entangled pair after matching measurements remains the diagonal cup. -/
theorem measured_mix : (Term.correlated .mix).eval zeros = Op.cup .bit := by
  have h := sound zeros
    (Proof.measuredCup (Γ := Context.empty presentation) .mix (Proof.law .mixEpi))
    (fun i => Fin.elim0 i)
  exact h.trans (Op.cup_copy .bit).symm

/-- The interpreted operations have nonzero outputs, excluding a trivial model. -/
theorem alice_mix_value (i : Fin 2) : (Term.alice .mix).eval zeros i () = 1 := by
  change Op.seq ((Term.correlated .mix).eval zeros) (Op.leftErase .bit) i () = 1
  rw [measured_mix]
  simp [Op.seq, Op.cup, Matrix.mul_apply, Fintype.sum_prod_type, Space.Basis]

/-- Cut preserves the interpretation of the concrete proof, using the common kernel theorem. -/
example : qkdMix.eval (model zeros) (fun i => Fin.elim0 i) =
    (qkdConditional .mix).eval (model zeros)
      (fun _ => (Proof.law (Γ := Context.empty presentation) .mixEpi).eval
        (model zeros) (fun i => Fin.elim0 i)) :=
  interpretation_substitute zeros (Δ := Context.empty presentation)
    (qkdConditional .mix) (fun _ => Proof.law .mixEpi) (fun i => Fin.elim0 i)

def ketZero : Op .unit .bit := fun i _ => if i = 0 then 1 else 0
def superposition : Op .unit .bit := Op.seq ketZero Op.mix

def twoIndependent : Op .unit (.tensor .bit .bit) :=
  Op.seq (Op.dagger (Op.unleft .unit)) (Op.tensor superposition superposition)

/-- Classical copying of a superposition differs from two copies of that state.
This is a concrete counterexample for this copy map, not the universal no-cloning theorem. -/
theorem classical_copy_not_clone : Op.seq superposition (Op.copy .bit) ≠ twoIndependent := by
  intro h
  have he := congrFun (congrFun h (0, 1)) ()
  norm_num [Op.seq, Op.copy, Op.basisMap, superposition, ketZero, Op.mix, twoIndependent,
    Op.dagger, Op.unleft, Op.tensor, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Space.Basis, Space.basisFintype,
    Space.basisDecidableEq, Complex.ext_iff] at he

/-- The concrete model refutes a false equation, so no closed derivation of
that equation exists in the presentation. -/
theorem no_zero_identity : IsEmpty (Proof (Context.empty presentation)
    (.variable .bit .bit 0) (.ident .bit)) where
  false d := by
    have h := sound zeros d (fun i => Fin.elim0 i)
    have he := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
    norm_num [Term.eval, zeros, Op.ident, Matrix.one_apply] at he

/-- Distinct constructors remain distinct proof trees even though their
interpretations are proofs of the same operation equality. -/
theorem distinct_proofs :
    (Proof.refl (Γ := Context.empty presentation) (Term.ident .bit)) ≠
      Proof.symm (Proof.refl (Γ := Context.empty presentation) (Term.ident .bit)) := by
  intro h
  cases h

-- A bit operation cannot be composed with a two-bit input interface.
#guard_msgs (drop info) in
#check_failure (Term.seq (Term.ident .bit) (Term.copy (.tensor .bit .bit)))

-- Equations about operations do not introduce state-copying constructors.
#guard_msgs (drop info) in
#check_failure (Term.copyQuantum : Term .bit (.tensor .bit .bit))

end
end Foundation.Quantum.Examples
