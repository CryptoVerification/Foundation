import Foundation.Crypto.Semantics.Probability.Facts
import Mathlib.Logic.Equiv.Prod

/-! Exposing one independent coordinate of a finite uniform function.
Refreshing a coordinate here is a distribution identity, not an operation
available to a random-oracle adversary. -/
namespace Foundation.Probability

set_option backward.isDefEq.respectTransparency false

variable {Domain Range Result : Type} [Fintype Domain] [DecidableEq Domain]
  [Fintype Range] [Nonempty Range]

theorem uniform_function_split (input : Domain) :
    uniform (Domain → Range) =
      (uniform Range).bind (fun value =>
        (uniform ({x : Domain // x ≠ input} → Range)).map
          (fun rest => (Equiv.funSplitAt input Range).symm (value, rest))) := by
  calc
    _ = (uniform (Range × ({x : Domain // x ≠ input} → Range))).map
        (Equiv.funSplitAt input Range).symm :=
      (uniform_map_equiv (Equiv.funSplitAt input Range).symm).symm
    _ = ((uniform Range).bind (fun value =>
        (uniform ({x : Domain // x ≠ input} → Range)).map (fun rest => (value, rest)))).map
        (Equiv.funSplitAt input Range).symm := by rw [uniform_pair]
    _ = _ := by simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Once the continuation no longer inspects the old value of one
coordinate, that coordinate can instead be sampled independently first. -/
theorem uniform_function_fresh (input : Domain)
    (f : Range → (Domain → Range) → ProbComp Result)
    (h : ∀ table value, f value (Function.update table input value) = f value table) :
    (uniform (Domain → Range)).bind (fun table => f (table input) table) =
      (uniform Range).bind (fun value => (uniform (Domain → Range)).bind (f value)) := by
  rw [uniform_function_split input]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext value
  rw [PMF.bind_comm]
  congr 1
  funext rest
  have he (old : Range) :
      Function.update ((Equiv.funSplitAt input Range).symm (old, rest)) input value =
        (Equiv.funSplitAt input Range).symm (value, rest) := by
    funext x
    by_cases hx : x = input
    · subst x; simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [Equiv.funSplitAt, Equiv.piSplitAt, hx]
  have hf (old : Range) :
      f value ((Equiv.funSplitAt input Range).symm (old, rest)) =
        f value ((Equiv.funSplitAt input Range).symm (value, rest)) :=
    (h _ value).symm.trans (congrArg (f value) (he old))
  simp_rw [hf]
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

/-- Refreshing one coordinate preserves the finite uniform function law.
This theorem does not expose a reprogramming interface to an adversary. -/
theorem uniform_function_resample (input : Domain) :
    (uniform (Domain → Range)).bind (fun table =>
      (uniform Range).map (fun value => Function.update table input value)) =
    uniform (Domain → Range) := by
  have h := uniform_function_fresh input
    (fun (value : Range) (table : Domain → Range) => PMF.pure (Function.update table input value))
    (by intro table value; simp)
  have hc := PMF.bind_comm (uniform (Domain → Range)) (uniform Range)
    (fun table value => PMF.pure (Function.update table input value))
  calc
    _ = _ := hc
    _ = _ := by simpa using h.symm

end Foundation.Probability
