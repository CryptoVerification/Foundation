import Foundation.Crypto.Semantics.Machine.ProgramRanking
import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.ProcedurePhysical

/-! One fixed native code with input-dependent assertions and ranks.
The logical input may occur in the proof of the postcondition without being
recovered from the endpoint or copied into machine memory. All results retain
the complete actual physical endpoint and its first-arrival time. -/
namespace Machine
open Foundation.Probability TimedExecution
universe u

structure Program.RankedFamily (code : Program) (Input : Type u) where
  assertions : Input → Program.Assertions
  verified : ∀ input, (assertions input).Verified code
  ranking : ∀ input, Program.Ranking (assertions input) code
  entry : Input → Configuration
  valid : ∀ input, (assertions input).Holds (entry input)

namespace Program.RankedFamily
variable {code : Program} {Input : Type u} (F : Program.RankedFamily code Input)

noncomputable def stage (input : Input) : TimedExecution.Procedure (stepPMF code) Unit Configuration :=
  (((F.ranking input).execution (F.verified input)).reindex
    (fun _ : Unit => ⟨F.entry input, F.valid input⟩)).physical

noncomputable def execution : TimedExecution.Procedure (stepPMF code) Input Configuration :=
  TimedExecution.Procedure.dispatch F.stage

noncomputable def native : Machine.Procedure Input Configuration := ⟨code, F.execution⟩

theorem execution_entry (input : Input) : F.execution.entry input = F.entry input := rfl

theorem exit (input : Input) (machine : Configuration) : F.execution.exit input machine = machine := rfl

theorem budget (input : Input) : F.execution.budget input = (F.ranking input).rank (F.entry input) + 1 := rfl

/-- Input-dependent proof labels disappear; full physical state and actual
arrival times remain jointly distributed exactly as in the native machine. -/
theorem costed (input : Input) : F.execution.costed input =
    runToBoundary (stepPMF code) Configuration.halted
      ((F.ranking input).rank (F.entry input) + 1) (F.entry input) :=
  TimedExecution.Ranking.costed (stepPMF code) Configuration.halted (F.assertions input).Holds
    (F.ranking input).rank (fun start hs _ => (F.verified input).preserves start hs)
    (F.ranking input).decreases ⟨F.entry input, F.valid input⟩

theorem halted (input : Input) (machine : Configuration)
    (h : machine ∈ (F.execution.semantics input).support) : machine.halted = true := by
  change machine ∈ ((((F.ranking input).execution (F.verified input)).semantics
    ⟨F.entry input, F.valid input⟩).map Subtype.val).support at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨result, _, rfl⟩ := h
  exact result.property.2

theorem postcondition (input : Input) (machine : Configuration)
    (h : machine ∈ (F.execution.semantics input).support) : (F.assertions input).Holds machine := by
  change machine ∈ ((((F.ranking input).execution (F.verified input)).semantics
    ⟨F.entry input, F.valid input⟩).map Subtype.val).support at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨result, _, rfl⟩ := h
  exact result.property.1

theorem stopped (input : Input) (machine : Configuration)
    (h : machine ∈ (F.execution.semantics input).support) :
    (F.assertions input).stopped machine.pc machine.inputTape machine.outputTape := by
  have hp := F.postcondition input machine h
  simpa only [Assertions.Holds, F.halted input machine h, ↓reduceIte] using hp

/-- This is actual reachability at the reported cost, not only a residual law. -/
theorem operational : TimedExecution.Procedure.Operational F.execution := by
  intro input result h
  rw [F.costed] at h
  exact runToBoundary_reachable (stepPMF code) Configuration.halted _ _ result h

theorem run (input : Input) (horizon : Nat)
    (hTime : (F.ranking input).rank (F.entry input) + 1 ≤ horizon) :
    evalConfigWithin code (F.entry input) horizon = F.execution.semantics input := by
  have h := F.native.final_run input (F.halted input) horizon hTime
  change evalConfigWithin code (F.entry input) horizon = (F.execution.semantics input).map id at h
  simpa only [PMF.map_id] using h

end Program.RankedFamily
end Machine
