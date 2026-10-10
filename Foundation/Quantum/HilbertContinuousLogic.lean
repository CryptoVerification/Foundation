import Foundation.Quantum.HilbertChannelNorm
import Foundation.Quantum.GeneralCPLogic

/-! The existing finite presentation interpreted in continuous operations on
the complete nuclear ideal. Infinite sums live in the semantics; proof trees
remain finite. No kernel extension or limit-introduction rule is required. -/
namespace Foundation.Quantum.Infinite.HilbertContinuousLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false
abbrev Term := GeneralCPLogic.Term
abbrev presentation := GeneralCPLogic.presentation
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def eval (σ : Nat → HilbertChannel E E) : Term → TraceClass E →L[ℂ] TraceClass E
  | .variable n => (σ n).continuous
  | .identity => ContinuousLinearMap.id ℂ (TraceClass E)
  | .seq f g => (eval σ g).comp (eval σ f)

def model (σ : Nat → HilbertChannel E E) : Model presentation where
  Carrier j := eval E σ j.1 = eval E σ j.2
  operation := fun r h => by
    cases r with
    | refl f => rfl
    | symm f g => exact (h 0).symm
    | trans f g k => exact (h 0).trans (h 1)
    | congr f g h' k => exact congrArg₂ ContinuousLinearMap.comp (h 1) (h 0)
    | assoc f g h => ext T; rfl
    | leftUnit f => ext T; rfl
    | rightUnit f => ext T; rfl

theorem sound (σ : Nat → HilbertChannel E E) {Γ : Context presentation} {j}
    (d : Derivation presentation Γ j) (h : ∀ i, (model E σ).Carrier (Γ.claim i)) :
    (model E σ).Carrier j := d.eval _ h

theorem interpretation_substitute (σ : Nat → HilbertChannel E E)
    {Γ Δ : Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model E σ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model E σ) h =
      d.eval (model E σ) (fun i => (r i).eval _ h) :=
  Derivation.eval_substitute _ h d r

/-- Every finite term commutes with a convergent sum in the nuclear norm. -/
theorem eval_tsum (σ : Nat → HilbertChannel E E) (t : Term) (u : ℕ → TraceClass E)
    (hu : Summable u) : eval E σ t (∑' n, u n) = ∑' n, eval E σ t (u n) :=
  (eval E σ t).map_tsum hu

def identityProof (t : Term) : Derivation presentation (.empty _) (.seq .identity t, t) :=
  .apply (T := presentation) (.leftUnit t) (fun i => Fin.elim0 i)

/-- A concrete derived operation still changes an actual normalized infinite-dimensional state. -/
theorem interpreted_pinching_changes :
    eval SequenceSpace (fun _ => coordinatePinching) (.seq .identity (.variable 0))
      coordinateSuperposition.state ≠ coordinateSuperposition.state := by
  change coordinatePinching.continuous coordinateSuperposition.state ≠ _
  rw [HilbertChannel.continuous_apply]
  exact coordinatePinching_changes_state

/-- The identity derivation is interpreted by the nontrivial continuous pinching model. -/
theorem pinching_identity_interpreted :
    eval SequenceSpace (fun _ => coordinatePinching) (.seq .identity (.variable 0)) =
      coordinatePinching.continuous :=
  sound SequenceSpace (fun _ => coordinatePinching) (identityProof (.variable 0)) (fun i => Fin.elim0 i)

end
end Foundation.Quantum.Infinite.HilbertContinuousLogic
