import Foundation.Crypto.Semantics.Oracle.RawTapeEquality
import Foundation.Crypto.Semantics.Oracle.CodeRelocation

/-! Restore the query delimiter and head after a raw candidate comparison.
The candidate table is not touched. Every erasure and head movement is charged;
the old Boolean comparison result is consumed by the caller's control branch. -/
namespace CryptoOracle.Interactive.RestoreRawQuery
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def actions (width : Nat) : List StraightLine.Action :=
  [.write .output none] ++ List.replicate width (.left .output)

def code (width : Nat) (tail : Code) : Code :=
  CodeRelocation.host (StraightLine.code (actions width)) tail

theorem code_length (width : Nat) (tail : Code) : (code width tail).length = width + 1 + tail.length := by
  simp [code, CodeRelocation.code_length, StraightLine.code, actions]

theorem code_native (width : Nat) (tail : Code) (ht : ∀ i ∈ tail, ∃ op, i = .native op) :
    ∀ i ∈ code width tail, ∃ op, i = .native op := by
  apply CodeRelocation.host_native _ _ _ ht
  intro i hi
  simp only [StraightLine.code, List.mem_map] at hi
  obtain ⟨action, _, he⟩ := hi
  exact ⟨StraightLine.instruction action, he.symm⟩

theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (query : List Bool)
    (input : Tape) (leftOutput outputTail : List (Option Bool)) (equal : Bool) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (code query.length tail) oracle) (query.length + 1)
      (⟨state, .running { inputTape := input, outputTape := { left := query.reverse.map some ++ leftOutput, current := some equal, right := outputTail } }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (StraightLine.code (actions query.length)).length
        (⟨state, .running { inputTape := input, outputTape := FixedWidthCopy.frontier leftOutput (query.map some ++ none :: outputTail) }, trace⟩ : Configuration State)) := by
  have hrun := StraightLine.public_run oracle state trace []
    (tail.map (CodeRelocation.instruction (StraightLine.code (actions query.length)).length))
    (actions query.length)
    { inputTape := input, outputTape := { left := query.reverse.map some ++ leftOutput, current := some equal, right := outputTail } }
    rfl rfl
  simp only [List.nil_append] at hrun
  have hlen : (actions query.length).length = query.length + 1 := by simp [actions]
  rw [hlen] at hrun
  have hrewind := StraightLine.rewind_output (query.map some) leftOutput outputTail none
    ({ pc := 1, inputTape := input } : Machine.Configuration)
  have hs : StraightLine.execute (actions query.length)
      { inputTape := input, outputTape := { left := query.reverse.map some ++ leftOutput, current := some equal, right := outputTail } } =
      { pc := query.length + 1, inputTape := input, outputTape := FixedWidthCopy.frontier leftOutput (query.map some ++ none :: outputTail) } := by
    simp only [actions, StraightLine.execute_append]
    simp only [StraightLine.execute, StraightLine.apply, Machine.Configuration.updateTape,
      Machine.Configuration.advance, Tape.write]
    simp only [List.length_map, ← List.map_reverse] at hrewind
    rw [hrewind]
    simp only [StraightLine.rewindOutputTape, FixedWidthCopy.frontier, ResponseLoading.fromCells]
    congr 1
    omega
  rw [hs] at hrun
  simpa only [code, CodeRelocation.host, CodeRelocation.frame, CodeRelocation.control,
    Machine.Configuration.rebasePc, StraightLine.code, actions, List.length_map,
    List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    Nat.add_zero, Nat.zero_add, Nat.add_comm] using hrun

end CryptoOracle.Interactive.RestoreRawQuery
