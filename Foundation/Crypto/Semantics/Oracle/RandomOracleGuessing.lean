import Foundation.Crypto.Semantics.Oracle.RandomOracle

/-! Unpredictability of an adaptively selected, previously unqueried input.
The adversary may make any number of repeated queries and use local coins.
This is a shared lemma for ROM games, not a MAC key-hiding argument.
-/
namespace CryptoOracle.RandomOracle

open Foundation.Probability
open scoped ENNReal

variable {Input Output : Type} [DecidableEq Input] [DecidableEq Output]
  [Fintype Output] [Nonempty Output]

noncomputable def freshGuessGame (attack : Program Input Output (Input × Output)) : ProbComp Bool :=
  (attack.run oracle []).bind fun out =>
    (oracle out.state out.result.1).map fun answer =>
      decide (out.result.1 ∉ out.trace.map Prod.fst) && decide (answer.2 = out.result.2)

/-- Even an adaptively chosen guess succeeds with probability at most one over
the response-space size, when winning requires a previously unqueried input. -/
theorem fresh_guess_bound (attack : Program Input Output (Input × Output)) :
    eventProb (freshGuessGame attack) (· = true) ≤ (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  apply eventProb_bind_le_of_support
  intro out ho
  by_cases hf : out.result.1 ∈ out.trace.map Prod.fst
  · simp [hf, eventProb]
  · have ht : out.state.lookup out.result.1 = none := by
      apply unqueried_fresh attack out ho
      intro output hm
      exact hf (List.mem_map.mpr ⟨(out.result.1, output), hm, rfl⟩)
    have he := congrArg (PMF.map (fun output : Output => decide (output = out.result.2)))
      (fresh_response out.state out.result.1 ht)
    have hm : (oracle out.state out.result.1).map
        (fun answer => decide (out.result.1 ∉ out.trace.map Prod.fst) &&
          decide (answer.2 = out.result.2)) =
        (uniform Output).map (fun output => decide (output = out.result.2)) := by
      simpa [hf, PMF.map_comp, Function.comp_def] using he
    rw [hm]
    exact le_of_eq (by simpa [eventProb] using uniform_guess out.result.2)

end CryptoOracle.RandomOracle
