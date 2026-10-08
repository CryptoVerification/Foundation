import Foundation.Crypto.Semantics.Machine.ProgramAssertions
import Foundation.Crypto.Semantics.Ranking

/-! Local ranking obligations for actual finite native code. Combined with
verified program assertions, they construct stopping contracts with actual
first-arrival costs. Input preparation remains an explicit physical entry. -/
namespace Machine
open Foundation.Probability TimedExecution

structure Program.Ranking (assertions : Program.Assertions) (code : Program) where
  rank : Configuration → Nat
  instruction : ∀ pc : Fin code.length, ∀ start : Configuration,
    start.pc = pc.val → start.halted = false → assertions.Holds start →
      (code[pc.val]).precondition
        (fun target => target.halted = true ∨ rank target < rank start) start

namespace Program.Ranking
variable {assertions : Program.Assertions} {code : Program} (ranking : Program.Ranking assertions code)

/-- The local proof covers both coin branches and implicit falloff halts. -/
theorem decreases (start : Configuration) (hStart : assertions.Holds start)
    (hActive : start.halted = false) (target : Configuration)
    (hTarget : target ∈ (stepPMF code start).support) (hUnfinished : target.halted = false) :
    ranking.rank target < ranking.rank start := by
  rcases (mem_support_stepPMF_iff code start target).mp hTarget with hs | ⟨hh, _⟩
  · by_cases hp : start.pc < code.length
    · have h := Instruction.precondition_step (List.getElem?_eq_getElem hp) hActive hs
        (ranking.instruction ⟨start.pc, hp⟩ start rfl hActive hStart)
      rcases h with h | h
      · simp [hUnfinished] at h
      · exact h
    · have hLookup : code[start.pc]? = none := List.getElem?_eq_none (by omega)
      have he : target = {start with halted := true} := by
        simpa [Step, successors, next, hActive, hLookup] using hs
      rw [he] at hUnfinished
      contradiction
  · simp [hActive] at hh

noncomputable def execution (verified : assertions.Verified code) :=
  TimedExecution.Ranking.procedure (stepPMF code) Configuration.halted assertions.Holds ranking.rank
    (fun start hs _ => verified.preserves start hs) ranking.decreases

/-- The input type represents admissible physical configurations only. -/
noncomputable def native (verified : assertions.Verified code) : Machine.Procedure
    {state // assertions.Holds state} {state // assertions.Holds state ∧ state.halted = true} :=
  ⟨code, ranking.execution verified⟩

/-- Arbitrary logical inputs can supply certified physical entries. This
reindexing performs no tape loading, copying or normalization. -/
noncomputable def onInputs {Input : Type*} (verified : assertions.Verified code)
    (entry : Input → Configuration) (hEntry : ∀ input, assertions.Holds (entry input)) :
    Machine.Procedure Input {state // assertions.Holds state ∧ state.halted = true} :=
  ⟨code, (ranking.execution verified).reindex (fun input => ⟨entry input, hEntry input⟩)⟩

theorem budget {Input : Type*} (verified : assertions.Verified code)
    (entry : Input → Configuration) (hEntry : ∀ input, assertions.Holds (entry input)) (input : Input) :
    (ranking.onInputs verified entry hEntry).execution.budget input = ranking.rank (entry input) + 1 := rfl

/-- The whole native execution agrees at every sufficient horizon. -/
theorem run {Input : Type*} (verified : assertions.Verified code)
    (entry : Input → Configuration) (hEntry : ∀ input, assertions.Holds (entry input))
    (input : Input) (horizon : Nat) (hTime : ranking.rank (entry input) + 1 ≤ horizon) :
    evalConfigWithin code (entry input) horizon =
      ((ranking.onInputs verified entry hEntry).execution.semantics input).map Subtype.val :=
  (ranking.onInputs verified entry hEntry).final_run input (fun output _ => output.property.2) horizon hTime

/-- The actual arrival time is retained rather than replaced by the rank cap. -/
theorem costed {Input : Type*} (verified : assertions.Verified code)
    (entry : Input → Configuration) (hEntry : ∀ input, assertions.Holds (entry input)) (input : Input) :
    ((ranking.onInputs verified entry hEntry).execution.costed input).map
      (fun result => (result.1.val, result.2)) =
      runToBoundary (stepPMF code) Configuration.halted (ranking.rank (entry input) + 1) (entry input) :=
  TimedExecution.Ranking.costed (stepPMF code) Configuration.halted assertions.Holds ranking.rank
    (fun start hs _ => verified.preserves start hs) ranking.decreases ⟨entry input, hEntry input⟩

theorem operational {Input : Type*} (verified : assertions.Verified code)
    (entry : Input → Configuration) (hEntry : ∀ input, assertions.Holds (entry input)) :
    TimedExecution.Procedure.Operational (ranking.onInputs verified entry hEntry).execution :=
  TimedExecution.Procedure.operational_reindex _ (TimedExecution.Ranking.operational _ _ _ _ _ _) _

end Program.Ranking
end Machine
