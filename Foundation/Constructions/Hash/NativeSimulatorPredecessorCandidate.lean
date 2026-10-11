import Foundation.Constructions.Hash.NativeSimulatorPredecessorFilter
import Foundation.Crypto.Semantics.Oracle.RestoreRawQuery

/-! The candidate-response stage after the data-marker branch. The actual raw
comparison halt is compiled to a return jump, so the caller can branch on the
computed equality flag and restore the raw target before examining another entry. -/
namespace Foundation.Hash.Native.SimulatorPredecessorCandidate
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def code (κ : Nat) (tail : Code) : Code :=
  SimulatorPredecessorFilter.advanceCode (2 * κ + 2) (HaltReturn.host RawTapeEquality.code tail)

theorem code_length (κ : Nat) (tail : Code) : (code κ tail).length = 2 * κ + 16 + tail.length := by
  simp only [code, SimulatorPredecessorFilter.advanceCode, CodeRelocation.code_length,
    StraightLine.code, List.length_map, List.length_replicate, HaltReturn.host_length,
    RawTapeEquality.code, NativeCode.code, RawTapeEquality.program_length]
  omega

theorem code_native (κ : Nat) (tail : Code) (ht : ∀ i ∈ tail, ∃ op, i = .native op) :
    ∀ i ∈ code κ tail, ∃ op, i = .native op := by
  apply CodeRelocation.host_native
  · intro i hi
    simp only [StraightLine.code, List.mem_map] at hi
    obtain ⟨action, _, he⟩ := hi
    exact ⟨StraightLine.instruction action, he.symm⟩
  · exact HaltReturn.host_native _ _ RawTapeEquality.code_native ht

/-- The caller receives the comparison result in finite control at the returned
address, while the complete original table and query remain on the tapes. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (code κ tail) oracle)
      (2 * κ + 2 + RawTapeEquality.steps entry.2.toList target.toList)
      (⟨state, .running { inputTape := FixedWidthCopy.frontier ((SimulatorPredecessorFilter.beforeMarker entry).reverse.map some ++ beforeInput) ((entry.1.2.1 :: SimulatorPredecessorFilter.afterMarker entry).map some ++ inputTail), outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (2 * κ + 2)
        (NativeCode.frame state trace ((RawTapeEquality.result
          (SimulatorPredecessorRecord.comparisonInput entry target beforeInput beforeOutput inputTail outputTail)).resumeAt RawTapeEquality.code.length))) := by
  let input := SimulatorPredecessorRecord.comparisonInput entry target beforeInput beforeOutput inputTail outputTail
  have hprepare := SimulatorPredecessorFilter.toResponse_run oracle state trace entry beforeInput inputTail
    (FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail))
    (HaltReturn.host RawTapeEquality.code tail)
  rw [code, TimedExecution.eval_add, hprepare, PMF.pure_bind,
    SimulatorPredecessorFilter.advanceCode]
  have placed := CodeRelocation.eval (StraightLine.code (List.replicate (2 * κ + 2) (.right .input)))
    (HaltReturn.host RawTapeEquality.code tail) oracle (RawTapeEquality.steps entry.2.toList target.toList)
    (NativeCode.frame state trace (RawTapeEquality.start input))
  rw [show (StraightLine.code (List.replicate (2 * κ + 2) (.right .input))).length = 2 * κ + 2 from by
    simp [StraightLine.code]] at placed
  have hstart : (⟨state, .running { inputTape := FixedWidthCopy.frontier ((SimulatorPredecessorRecord.header entry).reverse.map some ++ beforeInput) (entry.2.toList.map some ++ inputTail), outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }, trace⟩ : Configuration State) =
      NativeCode.frame state trace (RawTapeEquality.start input) := rfl
  rw [hstart]
  rw [placed]
  have called := RawTapeEquality.return_run oracle state trace input tail
  change TimedExecution.eval (Reification.timedStep (HaltReturn.host RawTapeEquality.code tail) oracle)
    (RawTapeEquality.steps entry.2.toList target.toList) (NativeCode.frame state trace (RawTapeEquality.start input)) = _ at called
  rw [called, PMF.pure_map]

/-- Exact continuation after comparison and target restoration. No table reset
or uncharged head movement occurs between these stages. -/
theorem restore_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (code κ (RestoreRawQuery.code n tail)) oracle)
      ((2 * κ + 2 + RawTapeEquality.steps entry.2.toList target.toList) + (n + 1))
      (⟨state, .running { inputTape := FixedWidthCopy.frontier ((SimulatorPredecessorFilter.beforeMarker entry).reverse.map some ++ beforeInput) ((entry.1.2.1 :: SimulatorPredecessorFilter.afterMarker entry).map some ++ inputTail), outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (2 * κ + 2) (CodeRelocation.frame RawTapeEquality.code.length
        (CodeRelocation.frame (StraightLine.code (RestoreRawQuery.actions n)).length
          (⟨state, .running { inputTape := FixedWidthCopy.frontier ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) inputTail, outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }, trace⟩ : Configuration State)))) := by
  let input := SimulatorPredecessorRecord.comparisonInput entry target beforeInput beforeOutput inputTail outputTail
  have h := run oracle state trace entry target beforeInput beforeOutput inputTail outputTail (RestoreRawQuery.code n tail)
  rw [TimedExecution.eval_add, h, PMF.pure_bind, code, SimulatorPredecessorFilter.advanceCode]
  have hresume : NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt RawTapeEquality.code.length) =
      CodeRelocation.frame RawTapeEquality.code.length (NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt 0)) := rfl
  change TimedExecution.eval _ _ (CodeRelocation.frame (2 * κ + 2)
    (NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt RawTapeEquality.code.length))) = _
  rw [hresume]
  have outer := CodeRelocation.eval (StraightLine.code (List.replicate (2 * κ + 2) (.right .input)))
    (HaltReturn.host RawTapeEquality.code (RestoreRawQuery.code n tail)) oracle (n + 1)
    (CodeRelocation.frame RawTapeEquality.code.length (NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt 0)))
  rw [show (StraightLine.code (List.replicate (2 * κ + 2) (.right .input))).length = 2 * κ + 2 from by
    simp [StraightLine.code]] at outer
  rw [outer, HaltReturn.body_eval]
  have hrestore := RestoreRawQuery.run oracle state trace target.toList
    (RawTapeEquality.result input).inputTape beforeOutput outputTail
    (decide (entry.2.toList = target.toList)) tail
  simp only [Bits.length_toList] at hrestore
  have hrestoreEntry : NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt 0) =
      (⟨state, .running { inputTape := (RawTapeEquality.result input).inputTape, outputTape := { left := target.toList.reverse.map some ++ beforeOutput, current := some (decide (entry.2.toList = target.toList)), right := outputTail } }, trace⟩ : Configuration State) := rfl
  rw [hrestoreEntry, hrestore, PMF.pure_map, PMF.pure_map]
  have htable : (RawTapeEquality.result input).inputTape =
      FixedWidthCopy.frontier ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) inputTail := by
    simp only [input, RawTapeEquality.result, RawTapeEquality.finish, SimulatorPredecessorRecord.comparisonInput]
    have hl : SimulatorLookup.entryBits entry = SimulatorPredecessorRecord.header entry ++ entry.2.toList := rfl
    rw [hl]
    simp [List.reverse_append, List.map_append, List.append_assoc]
  rw [htable]

/-- The result flag selects the found continuation or a charged target restore.
Both continuations have their internal addresses relocated when linked. -/
def callback (width : Nat) (found next : Code) : Code :=
  CodeRelocation.host [.native (.branch .output (1 + found.length) (1 + found.length) 1)]
    (CodeRelocation.host found (RestoreRawQuery.code width next))

def callbackRejectedPrefix (found : Code) : Code :=
  CodeRelocation.host [.native (.branch .output (1 + found.length) (1 + found.length) 1)] found

theorem callback_length (width : Nat) (found next : Code) :
    (callback width found next).length = width + 2 + found.length + next.length := by
  simp only [callback, CodeRelocation.code_length, RestoreRawQuery.code_length,
    List.length_cons, List.length_nil]
  omega

theorem callback_native (width : Nat) (found next : Code)
    (hf : ∀ i ∈ found, ∃ op, i = .native op) (hn : ∀ i ∈ next, ∃ op, i = .native op) :
    ∀ i ∈ callback width found next, ∃ op, i = .native op := by
  apply CodeRelocation.host_native
  · intro i hi
    exact ⟨.branch .output (1 + found.length) (1 + found.length) 1, by simpa using hi⟩
  · exact CodeRelocation.host_native _ _ hf (RestoreRawQuery.code_native _ _ hn)

theorem rejected_steps_bound (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n) :
    (2 * κ + 2 + RawTapeEquality.steps entry.2.toList target.toList) + (1 + (n + 1)) ≤
      6 * n + 2 * κ + 9 := by
  have hb := RawTapeEquality.steps_bound entry.2.toList target.toList (by simp)
  simp only [Bits.length_toList] at hb
  omega

theorem callback_rejected_host (width : Nat) (found next : Code) :
    callback width found next = CodeRelocation.host (callbackRejectedPrefix found) (RestoreRawQuery.code width next) := by
  rw [callback, ← CodeRelocation.host_assoc]
  rfl

theorem callbackRejectedPrefix_length (found : Code) :
    (callbackRejectedPrefix found).length = 1 + found.length := by
  rw [callbackRejectedPrefix, CodeRelocation.code_length]
  rfl

theorem callback_select (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (width : Nat) (found next : Code)
    (machine : Machine.Configuration) (equal : Bool)
    (hpc : machine.pc = 0) (ha : machine.halted = false)
    (hf : machine.outputTape.current = some equal) :
    TimedExecution.eval (Reification.timedStep (callback width found next) oracle) 1
      (NativeCode.frame state trace machine) =
      PMF.pure (NativeCode.frame state trace
        { machine with pc := if equal then 1 else 1 + found.length }) := by
  cases equal <;>
    simp [callback, CodeRelocation.host, TimedExecution.eval, Reification.timedStep,
      Reification.terminal, Reification.perform, Reification.action, transition, NativeCode.frame,
      hpc, ha, hf, Machine.Instruction.next, Machine.Configuration.tape]

/-- A true comparison result enters the found continuation with all cells intact. -/
theorem select_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) (found next : Code) :
    TimedExecution.eval (Reification.timedStep (code κ (callback n found next)) oracle)
      ((2 * κ + 2 + RawTapeEquality.steps entry.2.toList target.toList) + 1)
      (⟨state, .running { inputTape := FixedWidthCopy.frontier ((SimulatorPredecessorFilter.beforeMarker entry).reverse.map some ++ beforeInput) ((entry.1.2.1 :: SimulatorPredecessorFilter.afterMarker entry).map some ++ inputTail), outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (2 * κ + 2) (CodeRelocation.frame RawTapeEquality.code.length
        (NativeCode.frame state trace
          ((RawTapeEquality.result (SimulatorPredecessorRecord.comparisonInput entry target beforeInput beforeOutput inputTail outputTail)).resumeAt
            (if entry.2 = target then 1 else 1 + found.length))))) := by
  let input := SimulatorPredecessorRecord.comparisonInput entry target beforeInput beforeOutput inputTail outputTail
  have h := run oracle state trace entry target beforeInput beforeOutput inputTail outputTail (callback n found next)
  rw [TimedExecution.eval_add, h, PMF.pure_bind, code, SimulatorPredecessorFilter.advanceCode]
  have hr : NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt RawTapeEquality.code.length) =
      CodeRelocation.frame RawTapeEquality.code.length (NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt 0)) := rfl
  change TimedExecution.eval _ 1 (CodeRelocation.frame (2 * κ + 2)
    (NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt RawTapeEquality.code.length))) = _
  rw [hr]
  have outer := CodeRelocation.eval (StraightLine.code (List.replicate (2 * κ + 2) (.right .input)))
    (HaltReturn.host RawTapeEquality.code (callback n found next)) oracle 1
    (CodeRelocation.frame RawTapeEquality.code.length (NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt 0)))
  rw [show (StraightLine.code (List.replicate (2 * κ + 2) (.right .input))).length = 2 * κ + 2 from by
    simp [StraightLine.code]] at outer
  rw [outer, HaltReturn.body_eval, callback_select oracle state trace n found next
    ((RawTapeEquality.result input).resumeAt 0) (decide (entry.2.toList = target.toList)) rfl rfl rfl,
    PMF.pure_map, PMF.pure_map]
  simp only [Bits.toList, List.ofFn_inj]
  by_cases he : entry.2 = target <;> simp [he, input, Machine.Configuration.resumeAt]

/-- Consume a false result, restore the target and enter the caller's next code.
The input table is unchanged throughout this branch. -/
theorem callback_rejected_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (query : List Bool) (input : Tape)
    (leftOutput outputTail : List (Option Bool)) (found next : Code) :
    TimedExecution.eval (Reification.timedStep (callback query.length found next) oracle) (1 + (query.length + 1))
      (⟨state, .running { inputTape := input, outputTape := { left := query.reverse.map some ++ leftOutput, current := some false, right := outputTail } }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (callbackRejectedPrefix found).length
        (CodeRelocation.frame (StraightLine.code (RestoreRawQuery.actions query.length)).length
          (⟨state, .running { inputTape := input, outputTape := FixedWidthCopy.frontier leftOutput (query.map some ++ none :: outputTail) }, trace⟩ : Configuration State))) := by
  let machine : Machine.Configuration :=
    { inputTape := input, outputTape := { left := query.reverse.map some ++ leftOutput, current := some false, right := outputTail } }
  have selected := callback_select oracle state trace query.length found next machine false rfl rfl rfl
  change TimedExecution.eval _ (1 + (query.length + 1)) (NativeCode.frame state trace machine) = _
  rw [TimedExecution.eval_add, selected, PMF.pure_bind, callback_rejected_host]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hr : NativeCode.frame state trace { machine with pc := 1 + found.length } =
      CodeRelocation.frame (callbackRejectedPrefix found).length (NativeCode.frame state trace machine) := by
    simp [CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc,
      callbackRejectedPrefix_length, machine]
  rw [hr, CodeRelocation.eval]
  have restored := RestoreRawQuery.run oracle state trace query input leftOutput outputTail false next
  change TimedExecution.eval (Reification.timedStep (RestoreRawQuery.code query.length next) oracle)
    (query.length + 1) (NativeCode.frame state trace machine) = _ at restored
  rw [restored, PMF.pure_map]

/-- A nonmatching candidate is compared, rejected by the actual result branch,
and leaves the target restored for the next record. All stages run in one code. -/
theorem rejected_next_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) (found next : Code)
    (hne : entry.2 ≠ target) :
    TimedExecution.eval (Reification.timedStep (code κ (callback n found next)) oracle)
      ((2 * κ + 2 + RawTapeEquality.steps entry.2.toList target.toList) + (1 + (n + 1)))
      (⟨state, .running { inputTape := FixedWidthCopy.frontier ((SimulatorPredecessorFilter.beforeMarker entry).reverse.map some ++ beforeInput) ((entry.1.2.1 :: SimulatorPredecessorFilter.afterMarker entry).map some ++ inputTail), outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (2 * κ + 2) (CodeRelocation.frame RawTapeEquality.code.length
        (CodeRelocation.frame (callbackRejectedPrefix found).length
          (CodeRelocation.frame (StraightLine.code (RestoreRawQuery.actions n)).length
            (⟨state, .running { inputTape := FixedWidthCopy.frontier ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) inputTail, outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }, trace⟩ : Configuration State))))) := by
  let input := SimulatorPredecessorRecord.comparisonInput entry target beforeInput beforeOutput inputTail outputTail
  have h := run oracle state trace entry target beforeInput beforeOutput inputTail outputTail (callback n found next)
  rw [TimedExecution.eval_add, h, PMF.pure_bind, code, SimulatorPredecessorFilter.advanceCode]
  have hr : NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt RawTapeEquality.code.length) =
      CodeRelocation.frame RawTapeEquality.code.length (NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt 0)) := rfl
  change TimedExecution.eval _ (1 + (n + 1)) (CodeRelocation.frame (2 * κ + 2)
    (NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt RawTapeEquality.code.length))) = _
  rw [hr]
  have outer := CodeRelocation.eval (StraightLine.code (List.replicate (2 * κ + 2) (.right .input)))
    (HaltReturn.host RawTapeEquality.code (callback n found next)) oracle (1 + (n + 1))
    (CodeRelocation.frame RawTapeEquality.code.length (NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt 0)))
  rw [show (StraightLine.code (List.replicate (2 * κ + 2) (.right .input))).length = 2 * κ + 2 from by
    simp [StraightLine.code]] at outer
  rw [outer, HaltReturn.body_eval]
  have hf : decide (entry.2.toList = target.toList) = false := by
    simp [Bits.toList, List.ofFn_inj, hne]
  have hcallback := callback_rejected_run oracle state trace target.toList
    (RawTapeEquality.result input).inputTape beforeOutput outputTail found next
  simp only [Bits.length_toList] at hcallback
  have hentry : NativeCode.frame state trace ((RawTapeEquality.result input).resumeAt 0) =
      (⟨state, .running { inputTape := (RawTapeEquality.result input).inputTape, outputTape := { left := target.toList.reverse.map some ++ beforeOutput, current := some false, right := outputTail } }, trace⟩ : Configuration State) := by
    simp only [NativeCode.frame, Machine.Configuration.resumeAt, input, RawTapeEquality.result,
      RawTapeEquality.finish, SimulatorPredecessorRecord.comparisonInput, hf]
  rw [hentry, hcallback, PMF.pure_map, PMF.pure_map]
  have htable : (RawTapeEquality.result input).inputTape =
      FixedWidthCopy.frontier ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) inputTail := by
    simp only [input, RawTapeEquality.result, RawTapeEquality.finish, SimulatorPredecessorRecord.comparisonInput]
    have hl : SimulatorLookup.entryBits entry = SimulatorPredecessorRecord.header entry ++ entry.2.toList := rfl
    rw [hl]
    simp [List.reverse_append, List.map_append, List.append_assoc]
  rw [htable]

end Foundation.Hash.Native.SimulatorPredecessorCandidate
