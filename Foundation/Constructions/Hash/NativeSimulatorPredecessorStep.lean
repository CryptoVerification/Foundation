import Foundation.Constructions.Hash.NativeSimulatorPredecessorCandidate
import Foundation.Crypto.Semantics.Oracle.CodePrefixExecution

/-! One complete record step with four actual halt sites: found, table end,
rejected data entry, and skipped terminal entry. The latter two are the only
halts that the table-loop compiler will replace by a restart jump. -/
namespace Foundation.Hash.Native.SimulatorPredecessorStep
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def haltCode : Code := [.native .halt]

def missingActions (n : Nat) : List StraightLine.Action :=
  List.replicate n (.right .output) ++ [.write .output (some false)]

def missingCode (n : Nat) : Code := StraightLine.code (missingActions n) ++ haltCode

def dataCode (n κ : Nat) : Code :=
  SimulatorPredecessorCandidate.code κ (SimulatorPredecessorCandidate.callback n haltCode haltCode)

def terminalCode (n κ : Nat) : Code :=
  SimulatorPredecessorFilter.advanceCode (2 * κ + n + 2) haltCode

def guardCode (n κ : Nat) : Code :=
  SimulatorPredecessorFilter.guardedCode n (2 * n + 3)
    (2 * n + 3 + (dataCode n κ).length)
    (1 + (2 * n + 3 + (dataCode n κ).length + (terminalCode n κ).length))
    (2 * n + 3 + (dataCode n κ).length + (terminalCode n κ).length)

def code (n κ : Nat) : Code :=
  CodeRelocation.host (guardCode n κ)
    (CodeRelocation.host (dataCode n κ) (CodeRelocation.host (terminalCode n κ) (missingCode n)))

theorem dataCode_length (n κ : Nat) : (dataCode n κ).length = n + 2 * κ + 20 := by
  simp only [dataCode, SimulatorPredecessorCandidate.code_length,
    SimulatorPredecessorCandidate.callback_length, haltCode, List.length_cons, List.length_nil]
  omega

theorem terminalCode_length (n κ : Nat) : (terminalCode n κ).length = 2 * κ + n + 3 := by
  simp [terminalCode, SimulatorPredecessorFilter.advanceCode, CodeRelocation.code_length,
    StraightLine.code, haltCode]

theorem missingCode_length (n : Nat) : (missingCode n).length = n + 2 := by
  simp [missingCode, missingActions, StraightLine.code, haltCode]

theorem guardCode_length (n κ : Nat) : (guardCode n κ).length = 2 * n + 4 := by
  apply SimulatorPredecessorFilter.guardedCode_length

theorem code_length (n κ : Nat) : (code n κ).length = 5 * n + 4 * κ + 29 := by
  simp only [code, CodeRelocation.code_length, guardCode_length, dataCode_length,
    terminalCode_length, missingCode_length]
  omega

def dataStart (n κ : Nat) : Nat := (guardCode n κ).length
def terminalStart (n κ : Nat) : Nat := dataStart n κ + (dataCode n κ).length
def missingStart (n κ : Nat) : Nat := terminalStart n κ + (terminalCode n κ).length

def foundPc (n κ : Nat) : Nat := dataStart n κ + (2 * κ + 2) + RawTapeEquality.code.length + 1
def dataNextPc (n κ : Nat) : Nat := dataStart n κ + (dataCode n κ).length - 1
def terminalNextPc (n κ : Nat) : Nat := terminalStart n κ + (2 * κ + n + 2)
def missingPc (n κ : Nat) : Nat := missingStart n κ + n + 1

def queryTape (target : Bits n) (beforeOutput outputTail : List (Option Bool)) : Tape :=
  FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail)

def entryStart (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier beforeInput ((SimulatorLookup.entryBits entry).map some ++ inputTail),
    outputTape := queryTape target beforeOutput outputTail }

def markerStart (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier ((SimulatorPredecessorFilter.beforeMarker entry).reverse.map some ++ beforeInput)
      ((entry.1.2.1 :: SimulatorPredecessorFilter.afterMarker entry).map some ++ inputTail),
    outputTape := queryTape target beforeOutput outputTail }

def nextStart (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) inputTail,
    outputTape := queryTape target beforeOutput outputTail }

def foundStart (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) : Machine.Configuration :=
  { (nextStart entry target beforeInput beforeOutput inputTail outputTail) with
    outputTape := { left := target.toList.reverse.map some ++ beforeOutput, current := some true, right := outputTail } }

/-- The marker guard is a genuine active prefix of the complete step code. -/
theorem guard_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (2 * n + 4)
      (NativeCode.frame state trace (entryStart entry target beforeInput beforeOutput inputTail outputTail)) =
      PMF.pure (NativeCode.frame state trace
        { markerStart entry target beforeInput beforeOutput inputTail outputTail with
          pc := if entry.1.2.1 then terminalStart n κ else dataStart n κ }) := by
  have hg := SimulatorPredecessorFilter.guarded_run oracle state trace entry beforeInput inputTail
    (queryTape target beforeOutput outputTail)
    (2 * n + 3) (2 * n + 3 + (dataCode n κ).length)
    (1 + (2 * n + 3 + (dataCode n κ).length + (terminalCode n κ).length))
    (2 * n + 3 + (dataCode n κ).length + (terminalCode n κ).length)
  change TimedExecution.eval (Reification.timedStep (guardCode n κ) oracle) (1 + (2 * n + 3))
    (NativeCode.frame state trace (entryStart entry target beforeInput beforeOutput inputTail outputTail)) = _ at hg
  have ha := CodePrefixExecution.append_active (guardCode n κ)
    ((CodeRelocation.host (dataCode n κ) (CodeRelocation.host (terminalCode n κ) (missingCode n))).map
      (CodeRelocation.instruction (guardCode n κ).length)) oracle (1 + (2 * n + 3))
    (NativeCode.frame state trace (entryStart entry target beforeInput beforeOutput inputTail outputTail))
    (by intro finish hm; rw [hg, PMF.mem_support_pure_iff] at hm; subst finish; rfl)
  rw [show 2 * n + 4 = 1 + (2 * n + 3) from by omega]
  change TimedExecution.eval (Reification.timedStep (guardCode n κ ++ _ ) oracle) _ _ = _
  rw [ha, hg]
  simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
    NativeCode.frame, dataStart, terminalStart, guardCode_length, markerStart]
  have hp1 : 1 + (2 * n + 3) = 2 * n + 4 := by omega
  have hp2 : 1 + (2 * n + 3 + (dataCode n κ).length) = 2 * n + 4 + (dataCode n κ).length := by omega
  cases entry.1.2.1 <;> simp [hp1, hp2]

theorem terminalCode_link (n κ : Nat) (extra : Code) :
    CodeRelocation.host (terminalCode n κ) extra =
      SimulatorPredecessorFilter.advanceCode (2 * κ + n + 2) (CodeRelocation.host haltCode extra) := by
  simp only [terminalCode, SimulatorPredecessorFilter.advanceCode]
  rw [CodeRelocation.host_assoc]

/-- A terminal-marked record reaches the next-record halt with the query intact. -/
theorem terminal_before_halt (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool))
    (hm : entry.1.2.1 = true) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      ((2 * n + 4) + (2 * κ + n + 2))
      (NativeCode.frame state trace (entryStart entry target beforeInput beforeOutput inputTail outputTail)) =
      PMF.pure (NativeCode.frame state trace
        { nextStart entry target beforeInput beforeOutput inputTail outputTail with pc := terminalNextPc n κ }) := by
  rw [TimedExecution.eval_add, guard_run, hm, if_pos rfl, PMF.pure_bind]
  have hstart : NativeCode.frame state trace
      { markerStart entry target beforeInput beforeOutput inputTail outputTail with pc := terminalStart n κ } =
      CodeRelocation.frame (guardCode n κ).length
        (CodeRelocation.frame (dataCode n κ).length
          (NativeCode.frame state trace (markerStart entry target beforeInput beforeOutput inputTail outputTail))) := by
    simp [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
      NativeCode.frame, markerStart, terminalStart, dataStart]
  rw [hstart, code, CodeRelocation.eval, CodeRelocation.eval, terminalCode_link]
  have hskip := SimulatorPredecessorFilter.skipRemaining_run oracle state trace entry beforeInput inputTail
    (queryTape target beforeOutput outputTail) (CodeRelocation.host haltCode (missingCode n))
  change TimedExecution.eval _ (2 * κ + n + 2)
    (NativeCode.frame state trace (markerStart entry target beforeInput beforeOutput inputTail outputTail)) =
    PMF.pure (CodeRelocation.frame (2 * κ + n + 2)
      (NativeCode.frame state trace (nextStart entry target beforeInput beforeOutput inputTail outputTail))) at hskip
  rw [hskip, PMF.pure_map, PMF.pure_map]
  simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
    NativeCode.frame, nextStart, terminalNextPc, terminalStart, dataStart]
  simp only [Nat.add_assoc, Nat.add_zero]

theorem dataCode_link (n κ : Nat) (extra : Code) :
    CodeRelocation.host (dataCode n κ) extra = SimulatorPredecessorCandidate.code κ
      (SimulatorPredecessorCandidate.callback n haltCode (CodeRelocation.host haltCode extra)) := by
  rw [dataCode, SimulatorPredecessorCandidate.code_link, SimulatorPredecessorCandidate.callback_link]

theorem result_resume_layout (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) (pc : Nat) :
    (RawTapeEquality.result (SimulatorPredecessorRecord.comparisonInput entry target beforeInput beforeOutput inputTail outputTail)).resumeAt pc =
      { pc := pc, inputTape := FixedWidthCopy.frontier ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) inputTail,
        outputTape := { left := target.toList.reverse.map some ++ beforeOutput, current := some (decide (entry.2 = target)), right := outputTail } } := by
  have hl : SimulatorLookup.entryBits entry = SimulatorPredecessorRecord.header entry ++ entry.2.toList := rfl
  simp only [RawTapeEquality.result, RawTapeEquality.finish, SimulatorPredecessorRecord.comparisonInput,
    Machine.Configuration.resumeAt]
  rw [hl]
  simp [List.reverse_append, List.map_append, List.append_assoc, Bits.toList, List.ofFn_inj]

/-- A matching data record reaches the found halt, retaining the exact selected
entry on the input tape and the true result flag on the output tape. -/
theorem found_before_halt (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool))
    (hm : entry.1.2.1 = false) (he : entry.2 = target) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      ((2 * n + 4) + ((2 * κ + 2 + RawTapeEquality.steps entry.2.toList target.toList) + 1))
      (NativeCode.frame state trace (entryStart entry target beforeInput beforeOutput inputTail outputTail)) =
      PMF.pure (NativeCode.frame state trace
        { foundStart entry target beforeInput beforeOutput inputTail outputTail with pc := foundPc n κ }) := by
  rw [TimedExecution.eval_add, guard_run, hm]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [PMF.pure_bind]
  have hstart : NativeCode.frame state trace
      { markerStart entry target beforeInput beforeOutput inputTail outputTail with pc := dataStart n κ } =
      CodeRelocation.frame (guardCode n κ).length
        (NativeCode.frame state trace (markerStart entry target beforeInput beforeOutput inputTail outputTail)) := by
    simp [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
      NativeCode.frame, markerStart, dataStart]
  rw [hstart, code, CodeRelocation.eval, dataCode_link]
  have hdata := SimulatorPredecessorCandidate.select_run oracle state trace entry target
    beforeInput beforeOutput inputTail outputTail haltCode
    (CodeRelocation.host haltCode (CodeRelocation.host (terminalCode n κ) (missingCode n)))
  change TimedExecution.eval _ _
    (NativeCode.frame state trace (markerStart entry target beforeInput beforeOutput inputTail outputTail)) = _ at hdata
  rw [hdata, PMF.pure_map, if_pos he, result_resume_layout]
  simp only [he, decide_true]
  simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
    NativeCode.frame, foundStart, nextStart, foundPc, dataStart]
  simp only [Nat.add_assoc]

/-- A nonmatching data record reaches its next-record halt with the query head
and delimiter restored. The old record and the next marker are retained. -/
theorem rejected_before_halt (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool))
    (hm : entry.1.2.1 = false) (he : entry.2 ≠ target) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      ((2 * n + 4) + ((2 * κ + 2 + RawTapeEquality.steps entry.2.toList target.toList) + (1 + (n + 1))))
      (NativeCode.frame state trace (entryStart entry target beforeInput beforeOutput inputTail outputTail)) =
      PMF.pure (NativeCode.frame state trace
        { nextStart entry target beforeInput beforeOutput inputTail outputTail with pc := dataNextPc n κ }) := by
  rw [TimedExecution.eval_add, guard_run, hm]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [PMF.pure_bind]
  have hstart : NativeCode.frame state trace
      { markerStart entry target beforeInput beforeOutput inputTail outputTail with pc := dataStart n κ } =
      CodeRelocation.frame (guardCode n κ).length
        (NativeCode.frame state trace (markerStart entry target beforeInput beforeOutput inputTail outputTail)) := by
    simp [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
      NativeCode.frame, markerStart, dataStart]
  rw [hstart, code, CodeRelocation.eval, dataCode_link]
  have hdata := SimulatorPredecessorCandidate.rejected_next_run oracle state trace entry target
    beforeInput beforeOutput inputTail outputTail haltCode
    (CodeRelocation.host haltCode (CodeRelocation.host (terminalCode n κ) (missingCode n))) he
  change TimedExecution.eval _ _
    (NativeCode.frame state trace (markerStart entry target beforeInput beforeOutput inputTail outputTail)) = _ at hdata
  rw [hdata, PMF.pure_map]
  simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
    NativeCode.frame, SimulatorPredecessorCandidate.callbackRejectedPrefix_length,
    StraightLine.code, RestoreRawQuery.actions, List.length_map, List.length_append,
    List.length_replicate, haltCode, List.length_cons, List.length_nil,
    dataNextPc, dataStart, dataCode_length, nextStart, queryTape]
  have hp : (guardCode n κ).length + ((2 * κ + 2) + (RawTapeEquality.code.length + (1 + 1 + ((1 + n) + 0)))) =
      (guardCode n κ).length + (n + 2 * κ + 20) - 1 := by
    change _ + (_ + (14 + _)) = _
    omega
  rw [hp]

def missingPrefix (n κ : Nat) : Code :=
  CodeRelocation.host (CodeRelocation.host (guardCode n κ) (dataCode n κ)) (terminalCode n κ)

theorem missingPrefix_length (n κ : Nat) : (missingPrefix n κ).length = missingStart n κ := by
  simp [missingPrefix, CodeRelocation.code_length, missingStart, terminalStart, dataStart]

theorem code_missing_host (n κ : Nat) : code n κ = CodeRelocation.host (missingPrefix n κ) (missingCode n) := by
  rw [code, ← CodeRelocation.host_assoc, ← CodeRelocation.host_assoc]
  rfl

def emptyStart (target : Bits n) (beforeInput beforeOutput outputTail : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier beforeInput [some false], outputTape := queryTape target beforeOutput outputTail }

def missingState (target : Bits n) (beforeInput beforeOutput outputTail : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier beforeInput [some false],
    outputTape := { left := target.toList.reverse.map some ++ beforeOutput, current := some false, right := outputTail } }

theorem empty_guard_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (beforeInput beforeOutput outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) 1
      (NativeCode.frame state trace (emptyStart target beforeInput beforeOutput outputTail)) =
      PMF.pure (CodeRelocation.frame (missingPrefix n κ).length
        (NativeCode.frame state trace (emptyStart target beforeInput beforeOutput outputTail))) := by
  have hg := SimulatorPredecessorFilter.empty_run (n := n) (κ := κ) oracle state trace
    beforeInput (queryTape target beforeOutput outputTail)
    (2 * n + 3) (2 * n + 3 + (dataCode n κ).length)
    (1 + (2 * n + 3 + (dataCode n κ).length + (terminalCode n κ).length))
    (2 * n + 3 + (dataCode n κ).length + (terminalCode n κ).length)
  change TimedExecution.eval (Reification.timedStep (guardCode n κ) oracle) 1
    (NativeCode.frame state trace (emptyStart target beforeInput beforeOutput outputTail)) = _ at hg
  have ha := CodePrefixExecution.append_active (guardCode n κ)
    ((CodeRelocation.host (dataCode n κ) (CodeRelocation.host (terminalCode n κ) (missingCode n))).map
      (CodeRelocation.instruction (guardCode n κ).length)) oracle 1
    (NativeCode.frame state trace (emptyStart target beforeInput beforeOutput outputTail))
    (by intro finish hm; rw [hg, PMF.mem_support_pure_iff] at hm; subst finish; rfl)
  change TimedExecution.eval (Reification.timedStep (guardCode n κ ++ _) oracle) 1 _ = _
  rw [ha, hg]
  simp only [CodeRelocation.frame, CodeRelocation.control, NativeCode.frame,
    Machine.Configuration.rebasePc, missingPrefix_length, missingStart, terminalStart,
    dataStart, guardCode_length, emptyStart, Nat.add_zero]
  have hp : 1 + (2 * n + 3 + (dataCode n κ).length + (terminalCode n κ).length) =
      (2 * n + 4 + (dataCode n κ).length) + (terminalCode n κ).length := by omega
  rw [hp]

theorem missing_body_before_halt (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (input : Tape) (beforeOutput outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (missingCode n) oracle) (n + 1)
      (NativeCode.frame state trace { inputTape := input, outputTape := queryTape target beforeOutput outputTail }) =
      PMF.pure (NativeCode.frame state trace
        { pc := n + 1, inputTape := input, outputTape := { left := target.toList.reverse.map some ++ beforeOutput, current := some false, right := outputTail } }) := by
  have h := StraightLine.public_run oracle state trace [] haltCode (missingActions n)
    { inputTape := input, outputTape := queryTape target beforeOutput outputTail } rfl rfl
  simp only [List.nil_append] at h
  have hs := FixedWidthCopy.advance_output target.toList beforeOutput (none :: outputTail)
    ({ inputTape := input } : Machine.Configuration)
  simp only [Bits.length_toList] at hs
  simp only [missingActions, StraightLine.execute_append, queryTape, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil] at h
  rw [hs] at h
  simpa only [missingCode, missingActions, NativeCode.frame, StraightLine.execute, StraightLine.apply,
    Machine.Configuration.updateTape, Machine.Configuration.advance, Tape.write,
    FixedWidthCopy.frontier, ResponseLoading.fromCells, List.headD, List.tail_cons,
    queryTape, Nat.zero_add] using h

/-- Table exhaustion reaches the missing halt after writing a false result flag. -/
theorem empty_before_halt (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (beforeInput beforeOutput outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (1 + (n + 1))
      (NativeCode.frame state trace (emptyStart target beforeInput beforeOutput outputTail)) =
      PMF.pure (NativeCode.frame state trace
        { missingState target beforeInput beforeOutput outputTail with pc := missingPc n κ }) := by
  rw [TimedExecution.eval_add, empty_guard_run, PMF.pure_bind, code_missing_host,
    CodeRelocation.eval]
  have hb := missing_body_before_halt oracle state trace target
    (FixedWidthCopy.frontier beforeInput [some false]) beforeOutput outputTail
  change TimedExecution.eval _ (n + 1)
    (NativeCode.frame state trace (emptyStart target beforeInput beforeOutput outputTail)) = _ at hb
  rw [hb, PMF.pure_map]
  simp only [CodeRelocation.frame, CodeRelocation.control, NativeCode.frame,
    Machine.Configuration.rebasePc, missingPrefix_length, missingPc, missingState,
    Nat.add_assoc]

theorem data_last_halt (n κ : Nat) : (dataCode n κ)[(dataCode n κ).length - 1]? = some (.native .halt) := by
  let restored := RestoreRawQuery.code n haltCode
  have hr : restored[restored.length - 1]? = some (.native .halt) := by
    exact CodePrefixExecution.host_last_halt _ haltCode (by decide) rfl
  have hp : 0 < restored.length := by simp [restored, RestoreRawQuery.code_length, haltCode]
  have hbody := CodePrefixExecution.host_last_halt haltCode restored hp hr
  have hcb := CodePrefixExecution.host_last_halt
    [.native (.branch .output (1 + haltCode.length) (1 + haltCode.length) 1)]
    (CodeRelocation.host haltCode restored) (by rw [CodeRelocation.code_length]; omega) hbody
  change (SimulatorPredecessorCandidate.callback n haltCode haltCode)[(SimulatorPredecessorCandidate.callback n haltCode haltCode).length - 1]? = _ at hcb
  have hpCb : 0 < (SimulatorPredecessorCandidate.callback n haltCode haltCode).length := by
    rw [SimulatorPredecessorCandidate.callback_length]
    omega
  have hraw := CodePrefixExecution.host_last_halt
    (RawTapeEquality.code.map (HaltReturn.instruction RawTapeEquality.code.length))
    (SimulatorPredecessorCandidate.callback n haltCode haltCode) hpCb hcb
  have heq : CodeRelocation.host
      (RawTapeEquality.code.map (HaltReturn.instruction RawTapeEquality.code.length))
      (SimulatorPredecessorCandidate.callback n haltCode haltCode) =
      HaltReturn.host RawTapeEquality.code (SimulatorPredecessorCandidate.callback n haltCode haltCode) := by
    simp only [CodeRelocation.host, HaltReturn.host, List.length_map]
  rw [heq] at hraw
  have hpRaw : 0 < (HaltReturn.host RawTapeEquality.code (SimulatorPredecessorCandidate.callback n haltCode haltCode)).length := by
    rw [HaltReturn.host_length]
    omega
  exact CodePrefixExecution.host_last_halt _ _ hpRaw hraw

theorem data_next_halt (n κ : Nat) : (code n κ)[dataNextPc n κ]? = some (.native .halt) := by
  have hp : 0 < (dataCode n κ).length := by rw [dataCode_length]; omega
  have hi : (dataCode n κ).length - 1 < (dataCode n κ).length := by omega
  rw [code, dataNextPc, dataStart,
    show (guardCode n κ).length + (dataCode n κ).length - 1 =
      (guardCode n κ).length + ((dataCode n κ).length - 1) from by omega,
    CodeRelocation.lookup, CodeRelocation.lookup_prefix _ _ _ hi, data_last_halt]
  rfl

theorem terminal_next_halt (n κ : Nat) : (code n κ)[terminalNextPc n κ]? = some (.native .halt) := by
  have hh : (terminalCode n κ)[2 * κ + n + 2]? = some (.native .halt) := by
    rw [terminalCode, SimulatorPredecessorFilter.advanceCode]
    have hl : (StraightLine.code (List.replicate (2 * κ + n + 2) (.right .input))).length = 2 * κ + n + 2 := by
      simp [StraightLine.code]
    have fetched := CodeRelocation.lookup (StraightLine.code (List.replicate (2 * κ + n + 2) (.right .input))) haltCode 0
    rw [hl] at fetched
    have hmap : (haltCode[0]?).map (CodeRelocation.instruction (2 * κ + n + 2)) = some (.native .halt) := rfl
    simpa only [Nat.add_zero] using fetched.trans hmap
  have hi : 2 * κ + n + 2 < (terminalCode n κ).length := by rw [terminalCode_length]; omega
  rw [code, terminalNextPc, terminalStart, dataStart, Nat.add_assoc, CodeRelocation.lookup,
    CodeRelocation.lookup, CodeRelocation.lookup_prefix _ _ _ hi, hh]
  rfl

theorem missing_halt (n κ : Nat) : (code n κ)[missingPc n κ]? = some (.native .halt) := by
  have hh : (missingCode n)[n + 1]? = some (.native .halt) := by
    simp [missingCode, missingActions, StraightLine.code, haltCode]
  rw [code_missing_host, missingPc, ← missingPrefix_length, Nat.add_assoc,
    CodeRelocation.lookup, hh]
  rfl

theorem found_halt (n κ : Nat) : (code n κ)[foundPc n κ]? = some (.native .halt) := by
  have hcb : (SimulatorPredecessorCandidate.callback n haltCode haltCode)[1]? = some (.native .halt) := by
    rw [SimulatorPredecessorCandidate.callback]
    have fetched := CodeRelocation.lookup
      ([.native (.branch .output (1 + haltCode.length) (1 + haltCode.length) 1)] : Code)
      (CodeRelocation.host haltCode (RestoreRawQuery.code n haltCode)) 0
    rw [CodeRelocation.lookup_prefix _ _ 0 (by decide)] at fetched
    exact fetched
  have hd : (dataCode n κ)[(2 * κ + 2) + (RawTapeEquality.code.length + 1)]? = some (.native .halt) := by
    rw [dataCode, SimulatorPredecessorCandidate.code, SimulatorPredecessorFilter.advanceCode]
    have hl : (StraightLine.code (List.replicate (2 * κ + 2) (.right .input))).length = 2 * κ + 2 := by
      simp [StraightLine.code]
    have fetched := CodeRelocation.lookup (StraightLine.code (List.replicate (2 * κ + 2) (.right .input)))
      (HaltReturn.host RawTapeEquality.code (SimulatorPredecessorCandidate.callback n haltCode haltCode))
      (RawTapeEquality.code.length + 1)
    rw [hl, HaltReturn.body_lookup, hcb] at fetched
    exact fetched
  have hi : (2 * κ + 2) + (RawTapeEquality.code.length + 1) < (dataCode n κ).length := by
    rw [dataCode_length]
    change (2 * κ + 2) + (14 + 1) < _
    omega
  rw [code, foundPc, dataStart]
  rw [show (guardCode n κ).length + (2 * κ + 2) + RawTapeEquality.code.length + 1 =
      (guardCode n κ).length + ((2 * κ + 2) + (RawTapeEquality.code.length + 1)) from by omega]
  rw [CodeRelocation.lookup, CodeRelocation.lookup_prefix _ _ _ hi, hd]
  rfl

def recordTime (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n) : Nat :=
  (2 * n + 4) +
    if entry.1.2.1 then 2 * κ + n + 2 else
      if entry.2 = target then (2 * κ + 2 + RawTapeEquality.steps entry.2.toList target.toList) + 1
      else (2 * κ + 2 + RawTapeEquality.steps entry.2.toList target.toList) + (1 + (n + 1))

def recordBefore (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) : Machine.Configuration :=
  if entry.1.2.1 then
    { nextStart entry target beforeInput beforeOutput inputTail outputTail with pc := terminalNextPc n κ }
  else if entry.2 = target then
    { foundStart entry target beforeInput beforeOutput inputTail outputTail with pc := foundPc n κ }
  else
    { nextStart entry target beforeInput beforeOutput inputTail outputTail with pc := dataNextPc n κ }

theorem record_before_halt (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (recordTime entry target)
      (NativeCode.frame state trace (entryStart entry target beforeInput beforeOutput inputTail outputTail)) =
      PMF.pure (NativeCode.frame state trace (recordBefore entry target beforeInput beforeOutput inputTail outputTail)) := by
  cases hm : entry.1.2.1 with
  | true => simpa only [recordTime, recordBefore, hm, ↓reduceIte] using
      terminal_before_halt oracle state trace entry target beforeInput beforeOutput inputTail outputTail hm
  | false =>
      by_cases he : entry.2 = target
      · simpa only [recordTime, recordBefore, hm, Bool.false_eq_true, ↓reduceIte, he] using
          found_before_halt oracle state trace entry target beforeInput beforeOutput inputTail outputTail hm he
      · simpa only [recordTime, recordBefore, hm, Bool.false_eq_true, ↓reduceIte, he] using
          rejected_before_halt oracle state trace entry target beforeInput beforeOutput inputTail outputTail hm he

theorem recordBefore_active (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) :
    (recordBefore entry target beforeInput beforeOutput inputTail outputTail).halted = false := by
  simp only [recordBefore]
  split
  · rfl
  · split <;> rfl

theorem recordBefore_halt (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) :
    (code n κ)[(recordBefore entry target beforeInput beforeOutput inputTail outputTail).pc]? = some (.native .halt) := by
  simp only [recordBefore]
  split
  · exact terminal_next_halt n κ
  · split
    · exact found_halt n κ
    · exact data_next_halt n κ

theorem recordTime_bound (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n) :
    recordTime entry target + 1 ≤ 8 * n + 2 * κ + 14 := by
  have hb := RawTapeEquality.steps_bound entry.2.toList target.toList (by simp)
  simp only [Bits.length_toList] at hb
  unfold recordTime
  split
  · omega
  · split <;> omega

theorem pc_formulas (n κ : Nat) :
    foundPc n κ = 2 * n + 2 * κ + 21 ∧
    dataNextPc n κ = 3 * n + 2 * κ + 23 ∧
    terminalNextPc n κ = 4 * n + 4 * κ + 26 ∧
    missingPc n κ = 5 * n + 4 * κ + 28 := by
  simp only [foundPc, dataNextPc, terminalNextPc, missingPc, dataStart, terminalStart,
    missingStart, guardCode_length, dataCode_length, terminalCode_length,
    RawTapeEquality.code, NativeCode.code, List.length_map, RawTapeEquality.program_length]
  constructor
  · omega
  · constructor
    · omega
    · constructor <;> omega

theorem code_native (n κ : Nat) : ∀ op ∈ code n κ, ∃ native, op = .native native := by
  have hh : ∀ op ∈ haltCode, ∃ native, op = .native native := by
    intro op hm
    exact ⟨.halt, by simpa [haltCode] using hm⟩
  have hg : ∀ op ∈ guardCode n κ, ∃ native, op = .native native := by
    apply CodeRelocation.host_native
    · intro op hm
      exact ⟨_, by simpa using hm⟩
    · exact SimulatorPredecessorFilter.code_native _ _ _ _
  have hd : ∀ op ∈ dataCode n κ, ∃ native, op = .native native :=
    SimulatorPredecessorCandidate.code_native _ _ (SimulatorPredecessorCandidate.callback_native _ _ _ hh hh)
  have ht : ∀ op ∈ terminalCode n κ, ∃ native, op = .native native := by
    apply CodeRelocation.host_native _ _ _ hh
    intro op hm
    simp only [StraightLine.code, List.mem_map] at hm
    obtain ⟨action, _, he⟩ := hm
    exact ⟨_, he.symm⟩
  have hm : ∀ op ∈ missingCode n, ∃ native, op = .native native := by
    intro op hin
    simp only [missingCode, List.mem_append] at hin
    rcases hin with hin | hin
    · simp only [StraightLine.code, List.mem_map] at hin
      obtain ⟨action, _, he⟩ := hin
      exact ⟨_, he.symm⟩
    · exact hh op hin
  exact CodeRelocation.host_native _ _ hg (CodeRelocation.host_native _ _ hd
    (CodeRelocation.host_native _ _ ht hm))

end Foundation.Hash.Native.SimulatorPredecessorStep
