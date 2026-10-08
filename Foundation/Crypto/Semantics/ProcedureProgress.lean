import Foundation.Crypto.Semantics.ProcedurePhysical
import Foundation.Crypto.Semantics.ProcedureIteration

/-! Positive actual cost is independent of budget positivity. These rules
are for contracts that progress on every input; terminal-sensitive clients
apply them only on their proved nonterminal branches. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {Middle : Type w} {Output : Type x}
    {step : State → PMF State}

def Positive (P : Procedure step Input Output) : Prop :=
  ∀ input result, result ∈ (P.costed input).support → 0 < result.2

theorem positive_ofFixed (entry : Input → State) (exit : Input → Output → State)
    (semantics : Input → PMF Output) (duration : Input → Nat)
    (run : ∀ input, eval step (duration input) (entry input) = (semantics input).map (exit input))
    (hDuration : ∀ input, 0 < duration input) :
    Positive (Procedure.ofFixed step entry exit semantics duration run) := by
  intro input result hs
  change result ∈ ((semantics input).map (fun output => (output, duration input))).support at hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨output, _, he⟩ := hs
  subst result
  exact hDuration input

theorem positive_observe {Observed : Type*} (P : Procedure step Input Output) (hP : Positive P)
    (view : Output → Observed) (exit : Input → Observed → State)
    (hExit : ∀ input output, output ∈ (P.semantics input).support → exit input (view output) = P.exit input output) :
    Positive (P.observe view exit hExit) := by
  intro input result hs
  change result ∈ ((P.costed input).map (fun original => (view original.1, original.2))).support at hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨original, ho, he⟩ := hs
  subst result
  exact hP input original ho

theorem positive_physical (P : Procedure step Input Output) (hP : Positive P) : Positive P.physical := by
  intro input result hs
  rw [physical_costed, PMF.mem_support_map_iff] at hs
  obtain ⟨original, ho, he⟩ := hs
  subst result
  exact hP input original ho

set_option maxHeartbeats 1000000 in
/-- Any positive first component makes the composition positive, whatever
the second component's duration. The actual costs, rather than caps, add. -/
theorem positive_seq (first : Procedure step Input Middle) (second : Procedure step Middle Output)
    (hFirst : Positive first)
    (handoff : ∀ input middle, middle ∈ (first.semantics input).support → second.entry middle = first.exit input middle)
    (cap : Input → Nat)
    (hCap : ∀ input middle, middle ∈ (first.semantics input).support → second.budget middle ≤ cap input) :
    Positive (first.seq second handoff cap hCap) := by
  intro input result hs
  change result ∈ ((first.costed input).bind (fun middle => (second.costed middle.1).map
    (fun output => ((middle.1, output.1), middle.2 + output.2)))).support at hs
  rw [PMF.mem_support_bind_iff] at hs
  obtain ⟨middle, hm, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨output, _, he⟩ := hs
  subst result
  have hp := hFirst input middle hm
  omega

end Foundation.Probability.TimedExecution.Procedure
