import Foundation.Quantum.Syntax
import Foundation.Quantum.Finite

/-! The finite complex matrix model of the reconstructed object logic.
Every primitive law is verified, including the named example gate. -/
namespace Foundation.Quantum
open Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Assignment := (a b : Space) → Nat → Op a b

namespace Term

def eval (σ : Assignment) : {a b : Space} → Term a b → Op a b
  | _, _, .variable a b n => σ a b n
  | _, _, .mix => Op.mix
  | _, _, .ident a => Op.ident a
  | _, _, .seq f g => Op.seq (eval σ f) (eval σ g)
  | _, _, .tensor f g => Op.tensor (eval σ f) (eval σ g)
  | _, _, .dagger f => Op.dagger (eval σ f)
  | _, _, .conjugate f => Op.conjugate (eval σ f)
  | _, _, .name f => Op.name (eval σ f)
  | _, _, .copy a => Op.copy a
  | _, _, .erase a => Op.erase a
  | _, _, .cup a => Op.cup a
  | _, _, .cap a => Op.cap a
  | _, _, .swap a b => Op.swap a b
  | _, _, .assoc a b c => Op.assoc a b c
  | _, _, .unleft a => Op.unleft a
  | _, _, .unright a => Op.unright a
end Term

def Equation.Valid (σ : Assignment) (E : Equation) : Prop :=
  E.lhs.eval σ = E.rhs.eval σ

/-- Local soundness is an exhaustive verification of the syntactic schemes. -/
theorem Law.valid (σ : Assignment) (l : Law) : l.claim.Valid σ := by
  cases l with
  | refl f => rfl
  | idLeft f => exact Op.ident_seq _
  | idRight f => exact Op.seq_ident _
  | assoc f g h => exact Op.seq_assoc _ _ _
  | daggerDagger f => exact Op.dagger_dagger _
  | daggerSeq f g => exact Op.dagger_seq _ _
  | tensorSeq f g h k => exact Op.tensor_seq _ _ _ _
  | correlated m => exact Op.correlated_cup _
  | nameId a => exact Op.name_ident _
  | cupCopy a => exact Op.cup_copy _
  | leftCounit a => exact Op.copy_leftErase _
  | rightCounit a => exact Op.copy_rightErase _
  | special a => exact Op.copy_special _
  | coassoc a => exact Op.copy_coassoc _
  | cocomm a => exact Op.copy_comm _
  | frobenius a => exact Op.copy_frobenius _
  | snakeLeft a => exact Op.snake_left _
  | snakeRight a => exact Op.snake_right _
  | mixEpi => exact Op.mix_dagger_epi

/-- An actual instance of the existing meta-logic's Model. -/
def model (σ : Assignment) : Model presentation where
  Carrier := Equation.Valid σ
  operation := fun rule hs => match rule with
    | .law l => l.valid σ
    | .symm _ _ => (hs 0).symm
    | .trans _ _ _ => (hs 0).trans (hs 1)
    | .seqCong _ _ _ _ => congrArg₂ Op.seq (hs 0) (hs 1)
    | .tensorCong _ _ _ _ => congrArg₂ Op.tensor (hs 0) (hs 1)
    | .daggerCong _ _ => congrArg Op.dagger (hs 0)
    | .conjugateCong _ _ => congrArg Op.conjugate (hs 0)
    | .nameCong _ _ => congrArg Op.name (hs 0)

/-- Soundness for all finite derivations and any assignment of the variable gates. -/
theorem sound (σ : Assignment) {Γ : Context presentation} {E : Equation}
    (d : Derivation presentation Γ E) (h : ∀ i, (Γ.claim i).Valid σ) : E.Valid σ :=
  d.eval (model σ) h

/-- Interpretation of cut, specialized to this matrix semantics. -/
theorem interpretation_substitute (σ : Assignment) {Γ Δ : Context presentation}
    {E : Equation} (d : Derivation presentation Γ E)
    (replacement : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (Δ.claim i).Valid σ) :
    (d.substitute replacement).eval (model σ) h =
      d.eval (model σ) (fun i => (replacement i).eval (model σ) h) :=
  Derivation.eval_substitute (model σ) h d replacement

/-- Finite-dimensional, basis-chosen instance of Heunen 3.3.9, obtained by
interpreting the syntactic proof, not by a separate semantic shortcut. -/
theorem qkd_correct (σ : Assignment) {a b} (m : Term a b)
    (measurement : Op.seq (Op.dagger (m.eval σ)) (m.eval σ) = Op.ident b) :
    (Term.alice m).eval σ = (Term.bob m).eval σ :=
  sound σ (qkdConditional m) (fun _ => measurement)

/-- Different proof trees can express the same interpreted equation. This
semantics does not claim completeness or equality of proof trees. -/
theorem proof_irrelevance_of_interpretation (σ : Assignment) {Γ : Context presentation}
    {E : Equation} (d e : Derivation presentation Γ E) (h : ∀ i, (Γ.claim i).Valid σ) :
    d.eval (model σ) h = e.eval (model σ) h := Subsingleton.elim _ _

end
end Foundation.Quantum
