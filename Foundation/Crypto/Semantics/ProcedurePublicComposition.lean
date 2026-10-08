import Foundation.Crypto.Semantics.Procedure

/-! Public simulations compose while retaining the joint distribution of
outputs and actual costs. The intermediate public value chooses the next
public kernel; private values need not be recoverable from that view. -/
namespace Foundation.Probability.CostedComposition
universe u v
variable {Middle : Type u} {Output : Type v}

noncomputable def bind (first : PMF (Middle × Nat))
    (second : Middle → PMF (Output × Nat)) : PMF (Output × Nat) :=
  first.bind fun middle => (second middle.1).map fun output =>
    (output.1, middle.2 + output.2)

end Foundation.Probability.CostedComposition

namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x y z
variable {State : Type u} {Input : Type v} {Middle : Type w} {Output : Type x}
    {PublicMiddle : Type y} {PublicOutput : Type z} {step : State → PMF State}

/-- Local joint simulations give the joint public distribution of the real
sequential contract. Handoff and budgets are those required by `seq`. -/
theorem seq_public_cost (first : Procedure step Input Middle)
    (second : Procedure step Middle Output)
    (handoff : ∀ input middle, middle ∈ (first.semantics input).support →
      second.entry middle = first.exit input middle)
    (cap : Input → Nat)
    (hCap : ∀ input middle, middle ∈ (first.semantics input).support →
      second.budget middle ≤ cap input)
    (middleView : Middle → PublicMiddle) (outputView : Middle → Output → PublicOutput)
    (publicFirst : PMF (PublicMiddle × Nat))
    (publicSecond : PublicMiddle → PMF (PublicOutput × Nat))
    (input : Input)
    (hFirst : (first.costed input).map (fun result => (middleView result.1, result.2)) = publicFirst)
    (hSecond : ∀ middle, (second.costed middle).map
      (fun result => (outputView middle result.1, result.2)) = publicSecond (middleView middle)) :
    ((first.seq second handoff cap hCap).costed input).map
      (fun result => (outputView result.1.1 result.1.2, result.2)) =
      CostedComposition.bind publicFirst publicSecond := by
  unfold seq CostedComposition.bind
  rw [← hFirst]
  simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  congr 1
  funext middle
  have h := congrArg (fun distribution => distribution.map
    (fun result => (result.1, middle.2 + result.2))) (hSecond middle.1)
  simpa only [PMF.map_comp, Function.comp_def] using h

end Foundation.Probability.TimedExecution.Procedure
