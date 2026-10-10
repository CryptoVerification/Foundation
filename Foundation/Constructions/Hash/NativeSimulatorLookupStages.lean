import Foundation.Constructions.Hash.NativeSimulatorLookupCode

/-! Actual native stages of sequential simulator-table lookup. All stages
retain opaque external state and the complete existing transcript. -/
namespace Foundation.Hash.Native.SimulatorLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private def comparisonPrefix : Code := NativeCode.subroutinePrefix DelimitedTapeEquality.program
private def decision (n κ : Nat) : Code := [.native (.branch .input (faultPc n κ) 61 (foundPc n κ))]
private def skipPrefix (n κ : Nat) : Code := comparisonPrefix ++ decision n κ
private def foundPrefix (n κ : Nat) : Code :=
  skipPrefix n κ ++ StraightLine.code (skipActions n κ) ++ [.native (.jump (headerPc n κ))]
private def copyPrefix (n κ : Nat) : Code := foundPrefix n κ ++ StraightLine.code foundActions
private def missingPrefix (n κ : Nat) : Code :=
  copyPrefix n κ ++ FixedWidthCopy.code (copyPc n κ) n (faultPc n κ) ++ [.native .halt]
private def headerPrefix (n κ : Nat) : Code :=
  missingPrefix n κ ++ StraightLine.code (missingActions n κ) ++ [.native .halt]
private def headerCode (n κ : Nat) : Code :=
  [.native (.branch .input (faultPc n κ) (missingPc n κ) (headerPc n κ + 1)),
   .native (.moveRight .input), .native (.jump 0), .native .halt]

private theorem comparisonPrefix_length : comparisonPrefix.length = 60 := by
  rw [comparisonPrefix, NativeCode.subroutinePrefix_length, DelimitedTapeEquality.code_length]
private theorem skipPrefix_length (n κ : Nat) : (skipPrefix n κ).length = 61 := by
  simp [skipPrefix, decision, comparisonPrefix_length]
private theorem foundPrefix_length (n κ : Nat) : (foundPrefix n κ).length = foundPc n κ := by
  simp [foundPrefix, skipPrefix_length, StraightLine.code, foundPc]; omega
private theorem copyPrefix_length (n κ : Nat) : (copyPrefix n κ).length = copyPc n κ := by
  simp [copyPrefix, foundPrefix_length, StraightLine.code, copyPc]
private theorem missingPrefix_length (n κ : Nat) : (missingPrefix n κ).length = missingPc n κ := by
  simp [missingPrefix, copyPrefix_length, missingPc, Nat.add_assoc]
private theorem headerPrefix_length (n κ : Nat) : (headerPrefix n κ).length = headerPc n κ := by
  simp [headerPrefix, missingPrefix_length, StraightLine.code, headerPc]; omega

private theorem lookupCode_header (n κ : Nat) :
    lookupCode n κ = headerPrefix n κ ++ headerCode n κ := by
  simp [lookupCode, lookupTail, lookupBody, headerPrefix, missingPrefix,
    copyPrefix, foundPrefix, skipPrefix, comparisonPrefix, decision, headerCode, List.append_assoc]

private theorem header_instruction (n κ offset : Nat) :
    (lookupCode n κ)[headerPc n κ + offset]? = (headerCode n κ)[offset]? := by
  rw [lookupCode_header, ← headerPrefix_length, List.getElem?_append_right (by omega)]
  simp

/-- A record marker is consumed by three actual instructions: branch,
one-cell input movement, and a jump to the comparison subroutine. -/
theorem lookup_enter_record {State : Type*} (n κ : Nat)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (machine : Machine.Configuration)
    (pc : machine.pc = headerPc n κ) (active : machine.halted = false)
    (current : machine.inputTape.current = some true) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) 3
      (NativeCode.frame state trace machine) =
    PMF.pure (NativeCode.frame state trace
      { machine with pc := 0, inputTape := machine.inputTape.moveRight }) := by
  have first := lookup_header_step n κ oracle state trace machine true pc active current
  have move := header_instruction n κ 1
  have jump := header_instruction n κ 2
  simp only [headerCode, List.getElem?_cons_zero, List.getElem?_cons_succ] at move jump
  simp only [TimedExecution.eval, first, PMF.pure_bind, ↓reduceIte]
  simp [Reification.timedStep, Reification.terminal, NativeCode.frame,
    Reification.perform, Reification.action, transition, active, move, jump,
    Machine.Instruction.next, Machine.Configuration.advance, Machine.Configuration.updateTape,
    Nat.add_assoc, PMF.pure_bind]

/-- An entry point with the retained table on the input tape and a query
followed by a response-flag placeholder on the output tape. -/
def scanStart {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n))
    (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) : Machine.Configuration where
  pc := headerPc n κ
  inputTape := { Tape.ofBits (tableBits table) with left := beforeInput }
  outputTape := { Tape.ofBits (compressionPacket query ++ [false]) with left := beforeOutput }

/-- Consume an entry marker and compare its entire typed key. The result
retains both tapes, rather than exposing only the equality bit. -/
theorem lookup_compare_record {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n))
    (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle)
      (7 * (n + κ + 1) + 6)
      (NativeCode.frame state trace (scanStart (entry :: rest) query beforeInput beforeOutput)) =
    PMF.pure (NativeCode.frame state trace
      ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
        beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt 60)) := by
  rw [show 7 * (n + κ + 1) + 6 = 3 + (7 * (n + κ + 1) + 3) by omega,
    TimedExecution.eval_add]
  rw [lookup_enter_record n κ oracle state trace _ rfl rfl (by
    simp [scanStart, tableBits_cons, entryBits, Tape.ofBits]) , PMF.pure_bind]
  have start : ({ scanStart (entry :: rest) query beforeInput beforeOutput with
      pc := 0, inputTape := (scanStart (entry :: rest) query beforeInput beforeOutput).inputTape.moveRight } : Machine.Configuration) =
      DelimitedTapeEquality.start (comparisonInput entry.1 query (some true :: beforeInput)
        beforeOutput (entry.2.toList ++ tableBits rest) [false]) := by
    simp only [scanStart, tableBits_cons, entryBits, List.cons_append, List.append_assoc]
    change ({ pc := 0, inputTape := ({ Tape.ofBits (true :: (FiniteBitEncoding.delimit (compressionPacket entry.1) ++ (entry.2.toList ++ tableBits rest))) with left := beforeInput } : Tape).moveRight, outputTape := { Tape.ofBits (compressionPacket query ++ [false]) with left := beforeOutput } } : Machine.Configuration) = { pc := 0, inputTape := { Tape.ofBits (FiniteBitEncoding.delimit (compressionPacket entry.1) ++ (entry.2.toList ++ tableBits rest)) with left := some true :: beforeInput }, outputTape := { Tape.ofBits (compressionPacket query ++ [false]) with left := beforeOutput } }
    generalize FiniteBitEncoding.delimit (compressionPacket entry.1) ++
      (entry.2.toList ++ tableBits rest) = bits
    cases bits <;> rfl
  rw [start]
  simpa only [comparisonInput, compressionPacket_length] using
    lookup_comparison_run n κ oracle state trace
      (comparisonInput entry.1 query (some true :: beforeInput) beforeOutput
        (entry.2.toList ++ tableBits rest) [false])

private theorem frontier_ofBits (before : List (Option Bool)) (bits : List Bool) :
    FixedWidthCopy.frontier before (bits.map some) = { Tape.ofBits bits with left := before } := by
  cases bits <;> rfl

private theorem missing_execute (pc : Nat) (input : Tape) (before : List (Option Bool))
    (bits : List Bool) :
    StraightLine.execute (List.replicate bits.length (.right .output) ++
      [.write .output (some false), .right .output])
      { pc := pc, inputTape := input, outputTape := { Tape.ofBits (bits ++ [false]) with left := before } } =
      ({ pc := pc + bits.length + 2, inputTape := input, outputTape := { left := some false :: bits.reverse.map some ++ before } } : Machine.Configuration) := by
  rw [StraightLine.execute_append]
  have h := FixedWidthCopy.advance_output bits before [some false]
    ({ pc := pc, inputTape := input } : Machine.Configuration)
  simp only [← List.map_singleton, ← List.map_append, frontier_ofBits] at h
  rw [h]
  simp [StraightLine.execute, StraightLine.apply, Tape.ofBits, Tape.write, Tape.moveRight,
    Machine.Configuration.advance, Machine.Configuration.updateTape, Nat.add_assoc]

private theorem lookupCode_missing (n κ : Nat) :
    lookupCode n κ = missingPrefix n κ ++ StraightLine.code (missingActions n κ) ++
      [.native .halt] ++ headerCode n κ := by
  rw [lookupCode_header]
  rfl

theorem missing_halt_instruction (n κ : Nat) :
    (lookupCode n κ)[missingPc n κ + (n + κ + 1) + 2]? = some (.native .halt) := by
  have length : (missingPrefix n κ ++ StraightLine.code (missingActions n κ)).length =
      missingPc n κ + (n + κ + 1) + 2 := by
    simp [StraightLine.code, missingPrefix_length]; omega
  rw [lookupCode_missing, List.append_assoc]
  rw [← length, List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

/-- A missing result retains the query and writes the false response flag;
the input tape still contains the original end-of-table marker. -/
def missingFinish {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) : Machine.Configuration :=
  { scanStart [] query beforeInput beforeOutput with
    pc := missingPc n κ + (n + κ + 1) + 2
    outputTape := { left := some false :: (compressionPacket query).reverse.map some ++ beforeOutput }
    halted := true }

/-- Execute the absent branch to its actual native halt, with no host-side
lookup, table reset or manufactured result. -/
theorem lookup_missing_stage {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) (n + κ + 4 + halt.toNat)
      (NativeCode.frame state trace (scanStart [] query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace ({ missingFinish query beforeInput beforeOutput with halted := halt })) := by
  rw [show n + κ + 4 + halt.toNat = 1 + ((n + κ + 3) + halt.toNat) by omega, TimedExecution.eval_add]
  have dispatch := lookup_header_step n κ oracle state trace
    (scanStart [] query beforeInput beforeOutput) false rfl rfl rfl
  have firstRun : TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) 1
      (NativeCode.frame state trace (scanStart [] query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace
        { scanStart [] query beforeInput beforeOutput with pc := missingPc n κ }) := by
    simp [TimedExecution.eval, dispatch]
  rw [firstRun, PMF.pure_bind]
  rw [show n + κ + 3 = (missingActions n κ).length by simp, TimedExecution.eval_add]
  have run := StraightLine.public_run oracle state trace (missingPrefix n κ)
    ([.native .halt] ++ headerCode n κ) (missingActions n κ)
    ({ scanStart [] query beforeInput beforeOutput with pc := missingPc n κ } : Machine.Configuration)
    (by rw [missingPrefix_length]) rfl
  have host : missingPrefix n κ ++ StraightLine.code (missingActions n κ) ++
      ([.native .halt] ++ headerCode n κ) = lookupCode n κ := by
    rw [lookupCode_missing]; simp only [List.append_assoc]
  rw [host] at run
  simp only [NativeCode.frame] at ⊢
  rw [run, PMF.pure_bind]
  have execute : StraightLine.execute (missingActions n κ)
      { scanStart [] query beforeInput beforeOutput with pc := missingPc n κ } =
      { missingFinish query beforeInput beforeOutput with halted := false } := by
    simpa only [missingActions, scanStart, missingFinish, compressionPacket_length, tableBits_nil] using
      missing_execute (missingPc n κ) ({ Tape.ofBits [false] with left := beforeInput })
        beforeOutput (compressionPacket query)
  rw [execute]
  have instruction := missing_halt_instruction n κ
  cases halt <;> simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
    Reification.perform, Reification.action, transition, missingFinish,
    instruction, Machine.Instruction.next]

theorem lookup_missing_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (beforeInput beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) (n + κ + 5)
      (NativeCode.frame state trace (scanStart [] query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (missingFinish query beforeInput beforeOutput)) := by
  simpa only [Bool.toNat_true, Nat.add_assoc,
    show ({ missingFinish query beforeInput beforeOutput with halted := true } : Machine.Configuration) =
      missingFinish query beforeInput beforeOutput from rfl] using
    lookup_missing_stage oracle state trace query beforeInput beforeOutput true

private theorem found_execute (pc : Nat) (input : DelimitedTapeEquality.Input)
    (suffix : input.suffix = [false]) :
    StraightLine.execute foundActions ((DelimitedTapeEquality.finish input).resumeAt pc) =
      ({ pc := pc + 4,
         inputTape := FixedWidthCopy.frontier
           (some false :: (DelimitedTapeComparison.marked input.candidate).reverse.map some ++ input.beforeInput)
           (input.tail.map some),
         outputTape := { left := some true :: input.query.reverse.map some ++ input.beforeOutput } } : Machine.Configuration) := by
  cases tailEq : input.tail <;>
    simp [foundActions, StraightLine.execute, StraightLine.apply, DelimitedTapeEquality.finish,
      DelimitedTapeComparison.doneWithDecision, Configuration.resumeAt, suffix, tailEq,
      Tape.ofBits, Tape.write, Tape.moveRight, Configuration.updateTape, Configuration.advance,
      FixedWidthCopy.frontier, ResponseLoading.fromCells, Nat.add_assoc]

private theorem decision_instruction (n κ : Nat) :
    (lookupCode n κ)[60]? = some (.native (.branch .input (faultPc n κ) 61 (foundPc n κ))) := by
  simp [lookupCode, lookupTail, lookupBody, NativeCode.subroutinePrefix_length]

/-- The equality bit is consumed by the actual decision instruction. -/
theorem lookup_decision_step {State : Type*} (n κ : Nat)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (machine : Machine.Configuration) (bit : Bool)
    (pc : machine.pc = 60) (active : machine.halted = false)
    (current : machine.inputTape.current = some bit) :
    Reification.timedStep (lookupCode n κ) oracle (NativeCode.frame state trace machine) =
      PMF.pure (NativeCode.frame state trace
        { machine with pc := if bit then foundPc n κ else 61 }) := by
  have instruction : (lookupCode n κ)[machine.pc]? = some
      (.native (.branch .input (faultPc n κ) 61 (foundPc n κ))) := by
    rw [pc]; exact decision_instruction n κ
  cases bit <;> simp [Reification.timedStep, Reification.terminal, NativeCode.frame,
    Reification.perform, Reification.action, transition, active, instruction,
    Machine.Instruction.next, Machine.Configuration.tape, current]

private theorem lookupCode_found (n κ : Nat) :
    lookupCode n κ = foundPrefix n κ ++ StraightLine.code foundActions ++
      FixedWidthCopy.code (copyPc n κ) n (faultPc n κ) ++ [.native .halt] ++
      StraightLine.code (missingActions n κ) ++ [.native .halt] ++ headerCode n κ := by
  rw [lookupCode_header]
  simp only [headerPrefix, missingPrefix, copyPrefix, List.append_assoc]

private theorem lookupCode_copy (n κ : Nat) :
    lookupCode n κ = copyPrefix n κ ++ FixedWidthCopy.code (copyPc n κ) n (faultPc n κ) ++
      [.native .halt] ++ StraightLine.code (missingActions n κ) ++ [.native .halt] ++ headerCode n κ := by
  rw [lookupCode_header]
  simp only [headerPrefix, missingPrefix, List.append_assoc]

theorem found_halt_instruction (n κ : Nat) :
    (lookupCode n κ)[copyPc n κ + 7 * n]? = some (.native .halt) := by
  have length : (copyPrefix n κ ++ FixedWidthCopy.code (copyPc n κ) n (faultPc n κ)).length =
      copyPc n κ + 7 * n := by simp [copyPrefix_length]
  rw [lookupCode_copy, List.append_assoc, List.append_assoc, List.append_assoc]
  rw [← length, List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

/-- Final physical state of a matching entry. Its delimiter is restored,
the digest is copied at run time, and both original tape prefixes remain. -/
def foundFinish {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n)) (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) : Machine.Configuration where
  pc := copyPc n κ + 7 * n
  inputTape := FixedWidthCopy.frontier
    (entry.2.toList.reverse.map some ++ some false ::
      (DelimitedTapeComparison.marked (compressionPacket entry.1)).reverse.map some ++ some true :: beforeInput)
    ((tableBits rest).map some)
  outputTape := { left := entry.2.toList.reverse.map some ++ some true ::
    (compressionPacket query).reverse.map some ++ beforeOutput }
  halted := true

/-- Restore the key delimiter and copy the selected value, using the actual
fixed-width copying component. No value is embedded in the finite code. -/
theorem lookup_found_value_stage {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n)) (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) (5 * n + 4 + halt.toNat)
      (NativeCode.frame state trace
        ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
          beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt (foundPc n κ))) =
      PMF.pure (NativeCode.frame state trace ({ foundFinish entry rest query beforeInput beforeOutput with halted := halt })) := by
  let input := comparisonInput entry.1 query (some true :: beforeInput) beforeOutput
    (entry.2.toList ++ tableBits rest) [false]
  let afterCopy := [.native .halt] ++ StraightLine.code (missingActions n κ) ++ [.native .halt] ++ headerCode n κ
  have host : foundPrefix n κ ++ StraightLine.code foundActions ++
      (FixedWidthCopy.code (copyPc n κ) n (faultPc n κ) ++ afterCopy) = lookupCode n κ := by
    rw [lookupCode_found]; simp [afterCopy, List.append_assoc]
  have run := StraightLine.public_run oracle state trace (foundPrefix n κ)
    (FixedWidthCopy.code (copyPc n κ) n (faultPc n κ) ++ afterCopy)
    foundActions ((DelimitedTapeEquality.finish input).resumeAt (foundPc n κ))
    (by rw [foundPrefix_length]; rfl) rfl
  rw [host, found_execute _ _ rfl] at run
  simp only [input, foundActions_length] at run
  rw [show 5 * n + 4 + halt.toNat = 4 + (5 * n + halt.toNat) by omega, TimedExecution.eval_add]
  simp only [NativeCode.frame] at ⊢
  rw [run, PMF.pure_bind]
  have copier := FixedWidthCopy.run oracle state trace (copyPrefix n κ) afterCopy (faultPc n κ)
    (some false :: (DelimitedTapeComparison.marked (compressionPacket entry.1)).reverse.map some ++ some true :: beforeInput)
    (some true :: (compressionPacket query).reverse.map some ++ beforeOutput)
    ((tableBits rest).map some) entry.2.toList
  have copyHost : copyPrefix n κ ++ FixedWidthCopy.code (copyPrefix n κ).length entry.2.toList.length (faultPc n κ) ++
      afterCopy = lookupCode n κ := by
    rw [copyPrefix_length, Bits.length_toList, lookupCode_copy]; simp [afterCopy, List.append_assoc]
  rw [copyHost] at copier
  simp only [Bits.length_toList, copyPrefix_length] at copier
  rw [TimedExecution.eval_add]
  have prepared : ({ pc := foundPc n κ + 4, inputTape := FixedWidthCopy.frontier (some false :: (DelimitedTapeComparison.marked input.candidate).reverse.map some ++ input.beforeInput) (input.tail.map some), outputTape := { left := some true :: input.query.reverse.map some ++ input.beforeOutput } } : Machine.Configuration) = { pc := copyPc n κ, inputTape := FixedWidthCopy.frontier (some false :: (DelimitedTapeComparison.marked (compressionPacket entry.1)).reverse.map some ++ some true :: beforeInput) (entry.2.toList.map some ++ (tableBits rest).map some), outputTape := { left := some true :: (compressionPacket query).reverse.map some ++ beforeOutput } } := by
    simp only [input, comparisonInput, copyPc, List.map_append]
  rw [prepared, copier, PMF.pure_bind]
  have instruction := found_halt_instruction n κ
  cases halt <;> simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
    Reification.perform, Reification.action, transition, instruction,
    Machine.Instruction.next, foundFinish]

theorem lookup_found_value_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n)) (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) (5 * n + 5)
      (NativeCode.frame state trace
        ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
          beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt (foundPc n κ))) =
      PMF.pure (NativeCode.frame state trace (foundFinish entry rest query beforeInput beforeOutput)) := by
  simpa only [Bool.toNat_true, Nat.add_assoc,
    show ({ foundFinish entry rest query beforeInput beforeOutput with halted := true } : Machine.Configuration) =
      foundFinish entry rest query beforeInput beforeOutput from rfl] using
    lookup_found_value_stage oracle state trace entry rest query beforeInput beforeOutput true

/-- A matching head record is returned by actual execution, including the
entry marker, key comparison, equality branch, digest copy and native halt. -/
theorem lookup_found_stage {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n)) (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (equalKey : entry.1 = query) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle)
      (7 * (n + κ + 1) + 5 * n + 11 + halt.toNat)
      (NativeCode.frame state trace (scanStart (entry :: rest) query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace ({ foundFinish entry rest query beforeInput beforeOutput with halted := halt })) := by
  rw [show 7 * (n + κ + 1) + 5 * n + 11 + halt.toNat =
    (7 * (n + κ + 1) + 6) + (1 + (5 * n + 4 + halt.toNat)) by omega,
    TimedExecution.eval_add, lookup_compare_record, PMF.pure_bind, TimedExecution.eval_add]
  have dispatch := lookup_decision_step n κ oracle state trace
    ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
      beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt 60) true rfl rfl (by
        change (DelimitedTapeEquality.finish _).inputTape.current = some true
        rw [comparison_status, equalKey]; simp)
  have firstRun : TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) 1
      (NativeCode.frame state trace
        ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
          beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt 60)) =
      PMF.pure (NativeCode.frame state trace
        ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
          beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt (foundPc n κ))) := by
    simpa [TimedExecution.eval, Configuration.resumeAt] using
      congrArg (fun distribution => distribution.bind (TimedExecution.eval
        (Reification.timedStep (lookupCode n κ) oracle) 0)) dispatch
  rw [firstRun, PMF.pure_bind, lookup_found_value_stage]

theorem lookup_found_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n)) (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (equalKey : entry.1 = query) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle)
      (7 * (n + κ + 1) + 5 * n + 12)
      (NativeCode.frame state trace (scanStart (entry :: rest) query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (foundFinish entry rest query beforeInput beforeOutput)) := by
  simpa only [Bool.toNat_true, Nat.add_assoc,
    show ({ foundFinish entry rest query beforeInput beforeOutput with halted := true } : Machine.Configuration) =
      foundFinish entry rest query beforeInput beforeOutput from rfl] using
    lookup_found_stage oracle state trace entry rest query beforeInput beforeOutput equalKey true

private theorem entry_reverse {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (before : List (Option Bool)) :
    (entryBits entry).reverse.map some ++ before =
      entry.2.toList.reverse.map some ++ some false ::
        (DelimitedTapeComparison.marked (compressionPacket entry.1)).reverse.map some ++ some true :: before := by
  simp [entryBits, DelimitedTapeComparison.delimit_eq_marked,
    List.reverse_append, List.reverse_cons, List.map_append, List.append_assoc]

private theorem restore_execute (pc : Nat) (input : DelimitedTapeEquality.Input) :
    StraightLine.execute [.write .input (some false), .right .input]
      ((DelimitedTapeEquality.finish input).resumeAt pc) =
      ({ pc := pc + 2,
         inputTape := FixedWidthCopy.frontier
           (some false :: (DelimitedTapeComparison.marked input.candidate).reverse.map some ++ input.beforeInput)
           (input.tail.map some),
         outputTape := (DelimitedTapeEquality.finish input).outputTape } : Machine.Configuration) := by
  cases tailEq : input.tail <;>
    simp [StraightLine.execute, StraightLine.apply, DelimitedTapeEquality.finish,
      DelimitedTapeComparison.doneWithDecision, Configuration.resumeAt, tailEq,
      Tape.ofBits, Tape.write, Tape.moveRight, Configuration.updateTape, Configuration.advance,
      FixedWidthCopy.frontier, ResponseLoading.fromCells, Nat.add_assoc]

private theorem rewind_query (bits : List Bool) (before : List (Option Bool))
    (machine : Machine.Configuration) :
    StraightLine.execute (List.replicate bits.length (.left .output))
      { machine with outputTape := FixedWidthCopy.frontier (bits.reverse.map some ++ before) [some false] } =
      { machine with pc := machine.pc + bits.length, outputTape := { Tape.ofBits (bits ++ [false]) with left := before } } := by
  have h := StraightLine.rewind_output (bits.map some) before [] (some false) machine
  cases bits <;> simpa [FixedWidthCopy.frontier, ResponseLoading.fromCells,
    StraightLine.rewindOutputTape, Tape.ofBits] using h

private theorem skip_execute {n κ : Nat}
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n)) (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    StraightLine.execute (skipActions n κ)
      ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
        beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt 61) =
      { scanStart rest query ((entryBits entry).reverse.map some ++ beforeInput) beforeOutput with pc := 61 + (skipActions n κ).length } := by
  let input := comparisonInput entry.1 query (some true :: beforeInput) beforeOutput
    (entry.2.toList ++ tableBits rest) [false]
  rw [skipActions, StraightLine.execute_append, StraightLine.execute_append, restore_execute]
  let keyLeft := some false :: (DelimitedTapeComparison.marked (compressionPacket entry.1)).reverse.map some ++ some true :: beforeInput
  let queryEnd := FixedWidthCopy.frontier ((compressionPacket query).reverse.map some ++ beforeOutput) [some false]
  have prepared : ({ pc := 61 + 2, inputTape := FixedWidthCopy.frontier (some false :: (DelimitedTapeComparison.marked input.candidate).reverse.map some ++ input.beforeInput) (input.tail.map some), outputTape := (DelimitedTapeEquality.finish input).outputTape } : Machine.Configuration) =
      { pc := 63, inputTape := FixedWidthCopy.frontier keyLeft (entry.2.toList.map some ++ (tableBits rest).map some), outputTape := queryEnd } := by
    simp [input, comparisonInput, keyLeft, queryEnd, DelimitedTapeEquality.output_layout,
      FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.ofBits, List.map_append]
  change StraightLine.execute (List.replicate (n + κ + 1) (.left .output))
    (StraightLine.execute (List.replicate n (.right .input))
      ({ pc := 61 + 2, inputTape := FixedWidthCopy.frontier (some false :: (DelimitedTapeComparison.marked input.candidate).reverse.map some ++ input.beforeInput) (input.tail.map some), outputTape := (DelimitedTapeEquality.finish input).outputTape } : Machine.Configuration)) = _
  rw [prepared]
  have forward := FixedWidthCopy.advance_input entry.2.toList keyLeft ((tableBits rest).map some)
    ({ pc := 63, outputTape := queryEnd } : Machine.Configuration)
  simp only [Bits.length_toList] at forward
  rw [forward]
  have back := rewind_query (compressionPacket query) beforeOutput
    ({ pc := 63 + n, inputTape := FixedWidthCopy.frontier (entry.2.toList.reverse.map some ++ keyLeft) ((tableBits rest).map some) } : Machine.Configuration)
  simp only [compressionPacket_length] at back
  change StraightLine.execute (List.replicate (n + κ + 1) (.left .output))
    { pc := 63 + n, inputTape := FixedWidthCopy.frontier (entry.2.toList.reverse.map some ++ keyLeft) ((tableBits rest).map some), outputTape := queryEnd } = _
  change StraightLine.execute (List.replicate (n + κ + 1) (.left .output))
    { pc := 63 + n, inputTape := FixedWidthCopy.frontier (entry.2.toList.reverse.map some ++ keyLeft) ((tableBits rest).map some), outputTape := queryEnd } = _ at back
  rw [back]
  rw [entry_reverse]
  simp [scanStart, keyLeft, frontier_ofBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem lookupCode_skip (n κ : Nat) :
    lookupCode n κ = skipPrefix n κ ++ StraightLine.code (skipActions n κ) ++
      [.native (.jump (headerPc n κ))] ++ StraightLine.code foundActions ++
      FixedWidthCopy.code (copyPc n κ) n (faultPc n κ) ++ [.native .halt] ++
      StraightLine.code (missingActions n κ) ++ [.native .halt] ++ headerCode n κ := by
  rw [lookupCode_header]
  simp only [headerPrefix, missingPrefix, copyPrefix, foundPrefix, List.append_assoc]

private theorem skip_jump_instruction (n κ : Nat) :
    (lookupCode n κ)[61 + (skipActions n κ).length]? = some (.native (.jump (headerPc n κ))) := by
  have length : (skipPrefix n κ ++ StraightLine.code (skipActions n κ)).length =
      61 + (skipActions n κ).length := by simp [skipPrefix_length, StraightLine.code]
  rw [lookupCode_skip, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc]
  rw [← length, List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

/-- After a mismatch, restore the table delimiter, traverse the value,
rewind the query and jump to the next record marker. -/
theorem lookup_skip_value_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n)) (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) ((skipActions n κ).length + 1)
      (NativeCode.frame state trace
        ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
          beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt 61)) =
      PMF.pure (NativeCode.frame state trace
        (scanStart rest query ((entryBits entry).reverse.map some ++ beforeInput) beforeOutput)) := by
  let afterSkip := [.native (.jump (headerPc n κ))] ++ StraightLine.code foundActions ++
    FixedWidthCopy.code (copyPc n κ) n (faultPc n κ) ++ [.native .halt] ++
    StraightLine.code (missingActions n κ) ++ [.native .halt] ++ headerCode n κ
  have host : skipPrefix n κ ++ StraightLine.code (skipActions n κ) ++ afterSkip = lookupCode n κ := by
    rw [lookupCode_skip]; simp only [afterSkip, List.append_assoc]
  have run := StraightLine.public_run oracle state trace (skipPrefix n κ) afterSkip (skipActions n κ)
    ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
      beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt 61)
    (by rw [skipPrefix_length]; rfl) rfl
  rw [host, skip_execute] at run
  rw [TimedExecution.eval_add]
  simp only [NativeCode.frame] at ⊢
  rw [run, PMF.pure_bind]
  have instruction := skip_jump_instruction n κ
  simp only [skipActions_length] at instruction
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
    Reification.perform, Reification.action, transition, instruction,
    Machine.Instruction.next, scanStart]

/-- A nonmatching record is traversed by actual execution with its cells
restored, and the next scan inherits the original query and transcript. -/
theorem lookup_skip_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n)) (query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (unequalKey : entry.1 ≠ query) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle)
      (8 * (n + κ + 1) + n + 10)
      (NativeCode.frame state trace (scanStart (entry :: rest) query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace
        (scanStart rest query ((entryBits entry).reverse.map some ++ beforeInput) beforeOutput)) := by
  rw [show 8 * (n + κ + 1) + n + 10 =
    (7 * (n + κ + 1) + 6) + (1 + ((skipActions n κ).length + 1)) by
      rw [skipActions_length]; omega,
    TimedExecution.eval_add, lookup_compare_record, PMF.pure_bind, TimedExecution.eval_add]
  have dispatch := lookup_decision_step n κ oracle state trace
    ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
      beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt 60) false rfl rfl (by
        change (DelimitedTapeEquality.finish _).inputTape.current = some false
        rw [comparison_status]; simp [unequalKey])
  have firstRun : TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) 1
      (NativeCode.frame state trace
        ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
          beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt 60)) =
      PMF.pure (NativeCode.frame state trace
        ((DelimitedTapeEquality.finish (comparisonInput entry.1 query (some true :: beforeInput)
          beforeOutput (entry.2.toList ++ tableBits rest) [false])).resumeAt 61)) := by
    simpa [TimedExecution.eval, Configuration.resumeAt] using
      congrArg (fun distribution => distribution.bind (TimedExecution.eval
        (Reification.timedStep (lookupCode n κ) oracle) 0)) dispatch
  rw [firstRun, PMF.pure_bind, lookup_skip_value_run]

end Foundation.Hash.Native.SimulatorLookup
