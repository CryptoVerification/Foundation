import Foundation.Quantum.QKD.QuantumSampling
import Foundation.Quantum.QKD.SamplingBound

/-! Zero-tolerance error-pattern sampling of an arbitrary coherent joint state.
The ideal vector excludes large error patterns that escape the chosen sample.
This is a phase-sampling building block; it does not equate measured bit errors
of the prepare-and-measure BB84 experiment with unmeasured phase errors. -/
namespace Foundation.Quantum.QKD.QuantumErrorSampling
noncomputable section
open PureProjection SupportProjection Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {a : Space} {I : Type} [Fintype I] [DecidableEq I]

def good (U : Finset I) (bad : Nat) (pattern : a.Basis → Finset I)
    (T : Finset I) (i : a.Basis) : Prop :=
  ¬ Sampling.badUndetected U bad (pattern i,T)

instance (U : Finset I) (bad : Nat) (pattern : a.Basis → Finset I) (T : Finset I) :
    DecidablePred (good U bad pattern T) := fun i => inferInstanceAs
      (Decidable (¬ (bad ≤ (pattern i ∩ U).card ∧ Sampling.undetected (pattern i) T)))

omit [Fintype I] [DecidableEq I] in
theorem bound_finite (U : Finset I) (k bad : Nat) (hk : k ≤ U.card) :
    Sampling.missedErrorBound U k bad ≠ ⊤ := by
  apply ENNReal.div_ne_top
  · exact ENNReal.natCast_ne_top _
  · exact_mod_cast (Nat.choose_pos hk).ne'

omit [Fintype I] in
theorem classical (U : Finset I) (k bad : Nat) (hk : k ≤ U.card)
    (pattern : a.Basis → Finset I) (i : a.Basis) :
    (eventProb (Sampling.sample U k hk) (fun T => ¬ good U bad pattern T i)).toReal ≤
      (Sampling.missedErrorBound U k bad).toReal := by
  apply ENNReal.toReal_mono (bound_finite U k bad hk)
  have he : (fun T => ¬ good U bad pattern T i) =
      (fun T => bad ≤ (pattern i ∩ U).card ∧ Sampling.undetected (pattern i) T) := by
    funext T
    simp only [good, Sampling.badUndetected, not_not]
  rw [he]
  by_cases hb : bad ≤ (pattern i ∩ U).card
  · simpa only [hb, true_and] using Sampling.undetected_le U (pattern i) k bad hk hb
  · have hh : (fun T : Finset I => bad ≤ (pattern i ∩ U).card ∧ Sampling.undetected (pattern i) T) =
        (fun _ => False) := by funext T; simp only [hb, false_and]
    rw [hh]
    simp [eventProb]

/-- The actual public-sample joint operators satisfy the quantum square-root
error bound obtained from the exact finite-population classical theorem. -/
theorem approximation (U : Finset I) (k bad : Nat) (hk : k ≤ U.card)
    (pattern : a.Basis → Finset I) (v : a.Basis → ℂ) (hv : bracket v v = 1)
    (fallback : Finset I → a.Basis) :
    OperatorApprox (QuantumSampling.real (Sampling.sample U k hk) v)
      (QuantumSampling.ideal (Sampling.sample U k hk) (good U bad pattern) v fallback)
      (Real.sqrt (Sampling.missedErrorBound U k bad).toReal) :=
  QuantumSampling.approximation _ _ v hv fallback _ (classical U k bad hk pattern)

omit [Fintype I] in
/-- If a sample contains no error, every nonzero ideal amplitude has fewer
than `bad` errors in the population. This is a support statement, not a
conclusion about an unmeasured basis of an already measured BB84 state. -/
theorem accepted_support (U : Finset I) (bad : Nat) (pattern : a.Basis → Finset I)
    (T : Finset I) (v : a.Basis → ℂ) (fallback : a.Basis)
    (hf : good U bad pattern T fallback) (i : a.Basis)
    (hT : Sampling.undetected (pattern i) T)
    (hi : SupportProjection.vector (good U bad pattern T) v fallback i ≠ 0) :
    (pattern i ∩ U).card < bad := by
  by_contra h
  have hb : ¬ good U bad pattern T i := by
    change ¬ ¬ (bad ≤ (pattern i ∩ U).card ∧ Sampling.undetected (pattern i) T)
    exact not_not.mpr ⟨by omega,hT⟩
  exact hi (SupportProjection.supported _ v fallback hf i hb)

end
end Foundation.Quantum.QKD.QuantumErrorSampling
