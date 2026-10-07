import Foundation.Crypto.Semantics.Procedure

/-! Composition at a nonabsorbing physical exit. The first procedure samples
a bit; the second charges one transition to transfer it to the final state.
This example would fail if intermediate exits were silently frozen. -/
namespace Foundation.ProcedureCompositionExamples
open Foundation.Probability TimedExecution

inductive State where
  | initial
  | pending (bit : Bool)
  | finished (bit : Bool)

noncomputable def step : State → PMF State
  | .initial => sampleBit.map State.pending
  | .pending bit => PMF.pure (.finished bit)
  | .finished bit => PMF.pure (.finished bit)

noncomputable def sample : Procedure step Unit Bool :=
  Procedure.ofFixed step (fun _ => .initial) (fun _ => State.pending)
    (fun _ => sampleBit) (fun _ => 1) (fun _ => by simp [eval, step])

noncomputable def transfer : Procedure step Bool Bool :=
  Procedure.ofFixed step State.pending (fun _ => State.finished)
    PMF.pure (fun _ => 1) (fun bit => by simp [eval, step, PMF.pure_map])

noncomputable def composed : Procedure step Unit (Bool × Bool) :=
  sample.seq transfer (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem budget : composed.budget () = 2 := rfl

theorem cost_distribution : composed.costed () = sampleBit.map (fun bit => ((bit, bit), 2)) := by
  simp [composed, Procedure.seq, sample, transfer, Procedure.ofFixed, PMF.map,
    PMF.bind_bind, Function.comp_def]

theorem complete (extra : Nat) :
    eval step (2 + extra) (.initial) = sampleBit.map State.finished := by
  have h := composed.final_run () (fun output _ => rfl) (2 + extra) (by change 2 ≤ 2 + extra; omega)
  simpa [composed, Procedure.seq, sample, transfer, Procedure.ofFixed,
    PMF.map, PMF.bind_bind, Function.comp_def] using h

end Foundation.ProcedureCompositionExamples
