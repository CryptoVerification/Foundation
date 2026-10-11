import Foundation.Constructions.Hash.NativeSimulatorPredecessorRecord

/-! Read the original table entry's data/terminal marker without modifying the
table. A data marker is false; a terminal marker is true. Branch targets are
caller-supplied addresses in this component's frame. -/
namespace Foundation.Hash.Native.SimulatorPredecessorFilter
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def escaped (bits : List Bool) : List Bool := bits.flatMap (fun b => [true, b])

theorem delimit_append (first second : List Bool) :
    FiniteBitEncoding.delimit (first ++ second) = escaped first ++ FiniteBitEncoding.delimit second := by
  induction first with
  | nil => rfl
  | cons b rest ih => simp [FiniteBitEncoding.delimit, escaped, ih]

def beforeMarker (entry : CompressionInput (Bits κ) (Bits n) × Bits n) : List Bool :=
  true :: escaped entry.1.1.toList ++ [true]

def afterMarker (entry : CompressionInput (Bits κ) (Bits n) × Bits n) : List Bool :=
  FiniteBitEncoding.delimit entry.1.2.2.toList ++ entry.2.toList

theorem beforeMarker_length (entry : CompressionInput (Bits κ) (Bits n) × Bits n) :
    (beforeMarker entry).length = 2 * n + 2 := by
  have hlen (bits : List Bool) : (escaped bits).length = 2 * bits.length := by
    induction bits with
    | nil => rfl
    | cons bit rest ih => simp [escaped] at ih ⊢; omega
  simp [beforeMarker, hlen]

theorem entry_layout (entry : CompressionInput (Bits κ) (Bits n) × Bits n) :
    SimulatorLookup.entryBits entry = beforeMarker entry ++ entry.1.2.1 :: afterMarker entry := by
  simp [SimulatorLookup.entryBits, compressionPacket, beforeMarker, afterMarker,
    delimit_append, FiniteBitEncoding.delimit, List.append_assoc]

def actions (n : Nat) : List StraightLine.Action :=
  List.replicate (2 * n + 2) (.right .input)

def code (n data terminal malformed : Nat) : Code :=
  StraightLine.code (actions n) ++ [.native (.branch .input malformed data terminal)]

theorem code_length (n data terminal malformed : Nat) :
    (code n data terminal malformed).length = 2 * n + 3 := by
  simp [code, StraightLine.code, actions]

theorem code_native (n data terminal malformed : Nat) :
    ∀ i ∈ code n data terminal malformed, ∃ op, i = .native op := by
  intro i hi
  simp only [code, List.mem_append] at hi
  rcases hi with hi | hi
  · simp only [StraightLine.code, List.mem_map] at hi
    obtain ⟨action, _, he⟩ := hi
    exact ⟨StraightLine.instruction action, he.symm⟩
  · exact ⟨.branch .input malformed data terminal, by simpa using hi⟩

/-- The actual table marker selects data or terminal control flow. The complete
output tape (the runtime target) remains unchanged. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (beforeInput inputTail : List (Option Bool)) (output : Tape)
    (data terminal malformed : Nat) :
    TimedExecution.eval (Reification.timedStep (code n data terminal malformed) oracle) (2 * n + 3)
      (⟨state, .running { inputTape := FixedWidthCopy.frontier beforeInput ((SimulatorLookup.entryBits entry).map some ++ inputTail), outputTape := output }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := if entry.1.2.1 then terminal else data, inputTape := FixedWidthCopy.frontier ((beforeMarker entry).reverse.map some ++ beforeInput) ((entry.1.2.1 :: afterMarker entry).map some ++ inputTail), outputTape := output }, trace⟩ := by
  have hmove := StraightLine.public_run oracle state trace []
    [.native (.branch .input malformed data terminal)] (actions n)
    { inputTape := FixedWidthCopy.frontier beforeInput ((SimulatorLookup.entryBits entry).map some ++ inputTail), outputTape := output }
    rfl rfl
  simp only [List.nil_append, actions, List.length_replicate] at hmove
  have hs := FixedWidthCopy.advance_input (beforeMarker entry) beforeInput
    ((entry.1.2.1 :: afterMarker entry).map some ++ inputTail)
    ({ outputTape := output } : Machine.Configuration)
  rw [beforeMarker_length] at hs
  rw [entry_layout, List.map_append, List.append_assoc, hs] at hmove
  have hcode : StraightLine.code (List.replicate (2 * n + 2) (.right .input)) ++
      [.native (.branch .input malformed data terminal)] = code n data terminal malformed := rfl
  rw [hcode] at hmove
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by omega, TimedExecution.eval_add]
  rw [entry_layout, List.map_append, List.append_assoc, hmove, PMF.pure_bind]
  have fetched : (code n data terminal malformed)[2 * n + 2]? =
      some (.native (.branch .input malformed data terminal)) := by
    simp [code, StraightLine.code, actions]
  cases hm : entry.1.2.1 <;>
    simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, fetched,
      Machine.Instruction.next, Machine.Configuration.tape, FixedWidthCopy.frontier,
      ResponseLoading.fromCells]

/-- The suffix that must be crossed after a terminal entry is rejected. -/
theorem afterMarker_length (entry : CompressionInput (Bits κ) (Bits n) × Bits n) :
    (afterMarker entry).length = 2 * κ + 1 + n := by
  simp [afterMarker, FiniteBitEncoding.delimit_length]

/-- A charged input-only advance, linked to the caller's next stage. -/
def advanceCode (width : Nat) (tail : Code) : Code :=
  CodeRelocation.host (StraightLine.code (List.replicate width (.right .input))) tail

theorem advance_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (fields : List Bool)
    (beforeInput inputTail : List (Option Bool)) (output : Tape) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (advanceCode fields.length tail) oracle) fields.length
      (⟨state, .running { inputTape := FixedWidthCopy.frontier beforeInput (fields.map some ++ inputTail), outputTape := output }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (StraightLine.code (List.replicate fields.length (.right .input))).length
        (⟨state, .running { inputTape := FixedWidthCopy.frontier (fields.reverse.map some ++ beforeInput) inputTail, outputTape := output }, trace⟩ : Configuration State)) := by
  have hmove := StraightLine.public_run oracle state trace []
    (tail.map (CodeRelocation.instruction (StraightLine.code (List.replicate fields.length (.right .input))).length))
    (List.replicate fields.length (.right .input))
    { inputTape := FixedWidthCopy.frontier beforeInput (fields.map some ++ inputTail), outputTape := output }
    rfl rfl
  simp only [List.nil_append, List.length_replicate] at hmove
  have hs := FixedWidthCopy.advance_input fields beforeInput inputTail
    ({ outputTape := output } : Machine.Configuration)
  rw [hs] at hmove
  simpa only [advanceCode, CodeRelocation.host, CodeRelocation.frame, CodeRelocation.control,
    Machine.Configuration.rebasePc, StraightLine.code, List.length_map, List.length_replicate,
    Nat.add_zero, Nat.zero_add] using hmove

theorem header_layout (entry : CompressionInput (Bits κ) (Bits n) × Bits n) :
    SimulatorPredecessorRecord.header entry = beforeMarker entry ++
      (entry.1.2.1 :: FiniteBitEncoding.delimit entry.1.2.2.toList) := by
  simp [SimulatorPredecessorRecord.header, compressionPacket, beforeMarker, delimit_append,
    FiniteBitEncoding.delimit, List.append_assoc]

/-- After selecting a data entry, advance from its marker to its raw response.
The complete encoded key is retained and the query tape is untouched. -/
theorem toResponse_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (beforeInput inputTail : List (Option Bool)) (output : Tape) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (advanceCode (2 * κ + 2) tail) oracle) (2 * κ + 2)
      (⟨state, .running { inputTape := FixedWidthCopy.frontier ((beforeMarker entry).reverse.map some ++ beforeInput) ((entry.1.2.1 :: afterMarker entry).map some ++ inputTail), outputTape := output }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (2 * κ + 2)
        (⟨state, .running { inputTape := FixedWidthCopy.frontier ((SimulatorPredecessorRecord.header entry).reverse.map some ++ beforeInput) (entry.2.toList.map some ++ inputTail), outputTape := output }, trace⟩ : Configuration State)) := by
  let fields := entry.1.2.1 :: FiniteBitEncoding.delimit entry.1.2.2.toList
  have hl : fields.length = 2 * κ + 2 := by simp [fields, FiniteBitEncoding.delimit_length]
  have h := advance_run oracle state trace fields
    ((beforeMarker entry).reverse.map some ++ beforeInput) (entry.2.toList.map some ++ inputTail)
    output tail
  rw [hl] at h
  simpa only [afterMarker, fields, List.map_cons, List.map_append, List.cons_append, List.append_assoc,
    header_layout, List.reverse_append, StraightLine.code, List.length_map, List.length_replicate] using h

/-- Reject a terminal-marked entry and reach the next original record marker.
No part of the raw query or the private table is overwritten. -/
theorem skipRemaining_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (beforeInput inputTail : List (Option Bool)) (output : Tape) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (advanceCode (2 * κ + n + 2) tail) oracle) (2 * κ + n + 2)
      (⟨state, .running { inputTape := FixedWidthCopy.frontier ((beforeMarker entry).reverse.map some ++ beforeInput) ((entry.1.2.1 :: afterMarker entry).map some ++ inputTail), outputTape := output }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (2 * κ + n + 2)
        (⟨state, .running { inputTape := FixedWidthCopy.frontier ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) inputTail, outputTape := output }, trace⟩ : Configuration State)) := by
  have hl : (entry.1.2.1 :: afterMarker entry).length = 2 * κ + n + 2 := by
    rw [List.length_cons, afterMarker_length]
    omega
  have h := advance_run oracle state trace (entry.1.2.1 :: afterMarker entry)
    ((beforeMarker entry).reverse.map some ++ beforeInput) inputTail output tail
  rw [hl] at h
  simpa only [entry_layout, List.reverse_append, List.map_append, List.append_assoc,
    StraightLine.code, List.length_map, List.length_replicate] using h

/-- Check the record-list terminator before attempting to read a key marker.
The helper's branch addresses are relative to its own frame after this guard. -/
def guardedCode (n data terminal missing malformed : Nat) : Code :=
  CodeRelocation.host [.native (.branch .input missing missing 1)]
    (code n data terminal malformed)

theorem guardedCode_length (n data terminal missing malformed : Nat) :
    (guardedCode n data terminal missing malformed).length = 2 * n + 4 := by
  rw [guardedCode, CodeRelocation.code_length, code_length]
  simp
  omega

/-- An empty physical table selects the missing branch in one real instruction. -/
theorem empty_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (beforeInput : List (Option Bool)) (output : Tape)
    (data terminal missing malformed : Nat) :
    TimedExecution.eval (Reification.timedStep (guardedCode n data terminal missing malformed) oracle) 1
      (⟨state, .running { inputTape := FixedWidthCopy.frontier beforeInput ((SimulatorLookup.tableBits (n := n) (κ := κ) []).map some), outputTape := output }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := missing, inputTape := FixedWidthCopy.frontier beforeInput [some false], outputTape := output }, trace⟩ := by
  simp [guardedCode, CodeRelocation.host, TimedExecution.eval, Reification.timedStep,
    Reification.terminal, Reification.perform, Reification.action, transition,
    SimulatorLookup.tableBits_nil, FixedWidthCopy.frontier, ResponseLoading.fromCells,
    Machine.Instruction.next, Machine.Configuration.tape]

/-- For a real entry, the list-marker guard and key-marker selection are one
finite code. The table and complete target tape are retained on both branches. -/
theorem guarded_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (beforeInput inputTail : List (Option Bool)) (output : Tape)
    (data terminal missing malformed : Nat) :
    TimedExecution.eval (Reification.timedStep (guardedCode n data terminal missing malformed) oracle)
      (1 + (2 * n + 3))
      (⟨state, .running { inputTape := FixedWidthCopy.frontier beforeInput ((SimulatorLookup.entryBits entry).map some ++ inputTail), outputTape := output }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame 1
        (⟨state, .running { pc := if entry.1.2.1 then terminal else data, inputTape := FixedWidthCopy.frontier ((beforeMarker entry).reverse.map some ++ beforeInput) ((entry.1.2.1 :: afterMarker entry).map some ++ inputTail), outputTape := output }, trace⟩ : Configuration State)) := by
  let start : Configuration State :=
    ⟨state, .running { inputTape := FixedWidthCopy.frontier beforeInput ((SimulatorLookup.entryBits entry).map some ++ inputTail), outputTape := output }, trace⟩
  have hhead : TimedExecution.eval (Reification.timedStep (guardedCode n data terminal missing malformed) oracle) 1 start =
      PMF.pure (CodeRelocation.frame 1 start) := by
    simp [start, guardedCode, CodeRelocation.host, TimedExecution.eval, Reification.timedStep,
      Reification.terminal, Reification.perform, Reification.action, transition,
      SimulatorLookup.entryBits, FixedWidthCopy.frontier, ResponseLoading.fromCells,
      Machine.Instruction.next, Machine.Configuration.tape, CodeRelocation.frame,
      CodeRelocation.control, Machine.Configuration.rebasePc]
  change TimedExecution.eval _ (1 + (2 * n + 3)) start = _
  rw [TimedExecution.eval_add, hhead, PMF.pure_bind, guardedCode]
  have placed := CodeRelocation.eval [.native (.branch .input missing missing 1)]
    (code n data terminal malformed) oracle (2 * n + 3) start
  simp only [List.length_cons, List.length_nil] at placed
  rw [placed]
  have hmarker := run oracle state trace entry beforeInput inputTail output data terminal malformed
  change TimedExecution.eval (Reification.timedStep (code n data terminal malformed) oracle)
    (2 * n + 3) start = _ at hmarker
  rw [hmarker, PMF.pure_map]

end Foundation.Hash.Native.SimulatorPredecessorFilter
