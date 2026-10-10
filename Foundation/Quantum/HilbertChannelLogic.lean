import Foundation.Quantum.HilbertChannel
import Foundation.Quantum.GeneralCPLogic

/-! The existing finite equational presentation is also interpreted by concrete
trace-class operations on arbitrary Hilbert spaces. This does not conflate
proof-tree equality with equality of operators. -/
namespace Foundation.Quantum.Infinite.HilbertChannelLogic
open Foundation.Logic
abbrev Term := GeneralCPLogic.Term
abbrev presentation := GeneralCPLogic.presentation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def eval (σ : Nat → HilbertChannel E E) : Term → TraceClass E → TraceClass E
  | .variable n => (σ n).apply
  | .identity => id
  | .seq f g => eval σ g ∘ eval σ f

def model (σ : Nat → HilbertChannel E E) : Model presentation where
  Carrier j := ∀ T, eval E σ j.1 T = eval E σ j.2 T
  operation := fun r h => match r with
    | .refl _ => fun _ => rfl
    | .symm .. => fun T => (h 0 T).symm
    | .trans .. => fun T => (h 0 T).trans (h 1 T)
    | .congr f g h' k => fun T => by
      change eval E σ h' (eval E σ f T) = eval E σ k (eval E σ g T)
      exact (congrArg (eval E σ h') (h 0 T)).trans (h 1 (eval E σ g T))
    | .assoc .. => fun _ => rfl
    | .leftUnit .. => fun _ => rfl
    | .rightUnit .. => fun _ => rfl

theorem sound (σ : Nat → HilbertChannel E E) {Γ : Context presentation} {j}
    (d : Derivation presentation Γ j) (h : ∀ i, (model E σ).Carrier (Γ.claim i)) :
    (model E σ).Carrier j := d.eval (model E σ) h

theorem interpretation_substitute (σ : Nat → HilbertChannel E E)
    {Γ Δ : Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model E σ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model E σ) h =
      d.eval (model E σ) (fun i => (r i).eval (model E σ) h) :=
  Derivation.eval_substitute (model E σ) h d r

end
end Foundation.Quantum.Infinite.HilbertChannelLogic
