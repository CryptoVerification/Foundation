import Foundation.Crypto.Semantics.Machine.EncodedPolynomialObserver
import Foundation.Crypto.Semantics.Probability.ObserverBound

/-! Relate semantic observer bounds to actual fixed-code polynomial observers
of a supplied encoding. Efficiency of computing the encoding is not inferred.
This applies to arbitrary represented value types and cryptographic schemes. -/
namespace Machine.PolynomialObserver
open Foundation.Probability
open scoped ENNReal
universe u
variable {Value : Type u}

/-- The same experiment can be described before or after its supplied encoding. -/
theorem encoded_observerGap (E : FiniteBitEncoding Value) (left right : PMF Value) (O : PolynomialObserver) :
    observerGap left right (fun value => O.observe (E.encode value)) =
      observerGap (left.map E.encode) (right.map E.encode) O.observe := by
  simp only [observerGap, PMF.bind_map, Function.comp_def]

/-- Class membership is discharged by a real polynomial machine witness. -/
theorem encoded_bound_iff (E : FiniteBitEncoding Value) (left right : PMF Value) (epsilon : ℝ≥0∞) :
    ObserverBound (encodedClass E) left right epsilon ↔
      ∀ observer : PolynomialObserver,
        observerGap (left.map E.encode) (right.map E.encode) observer.observe ≤ epsilon := by
  constructor
  · intro bound observer
    rw [← encoded_observerGap]
    exact bound _ ⟨observer, rfl⟩
  · intro bound kernel hKernel
    obtain ⟨observer, rfl⟩ := hKernel
    rw [encoded_observerGap]
    exact bound observer

/-- Information-theoretic equality supplies the concrete advantage bound zero. -/
theorem encoded_bound_zero_of_eq (E : FiniteBitEncoding Value) (left right : PMF Value) (same : left = right) :
    ObserverBound (encodedClass E) left right 0 := ObserverBound.of_eq _ same

end Machine.PolynomialObserver
