import Foundation.Constructions.Hash.NativeSimulatorKeyComparison
import Foundation.Crypto.Semantics.Oracle.MarkedBackwardCopy
import Foundation.Crypto.Semantics.Oracle.NativeCodeOracleIndependence
import Foundation.Crypto.Semantics.Oracle.NativePacketComponentResources
import Foundation.Crypto.Semantics.BoundaryExactTime

/-! Prepend a runtime compression entry to the physical simulator table.
The entry key and value are read from the output tape, not embedded in code.
The entry precondition places the old table at the input head with an empty
left prefix; preparing that layout is a separate caller obligation. -/
namespace Foundation.Hash.Native.SimulatorRemember
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private def initActions : List StraightLine.Action := [.left .input, .left .output]
private def delimiterActions : List StraightLine.Action := [.write .input (some false), .left .input]

def keyPc (n : Nat) : Nat := 4 + 7 * n
def haltPc (n κ : Nat) : Nat := keyPc n + 9 * (n + κ + 1) + 1
def faultPc (n κ : Nat) : Nat := haltPc n κ + 1

/-- Typed execution reaches the first continuation instruction after the
record write. The caller chooses an explicit error address for malformed data. -/
def codeWithContinuation (n κ fault : Nat) (tail : Code) : Code :=
  StraightLine.code initActions ++ FixedWidthCopy.codeWith true true 2 n fault ++
  StraightLine.code delimiterActions ++ MarkedBackwardCopy.code (keyPc n) (n + κ + 1) fault ++
  [.native (.write .input true)] ++ tail

def code (n κ : Nat) : Code := codeWithContinuation n κ (faultPc n κ) [.native .halt, .native .halt]

theorem code_length (n κ : Nat) : (code n κ).length = 16 * n + 9 * κ + 16 := by
  simp [code, codeWithContinuation, StraightLine.code, initActions, delimiterActions]; omega

theorem codeWithContinuation_native (n κ fault : Nat) (tail : Code)
    (hTail : ∀ instruction ∈ tail, ∃ native, instruction = .native native) :
    ∀ instruction ∈ codeWithContinuation n κ fault tail, ∃ native, instruction = .native native := by
  intro instruction member
  simp only [codeWithContinuation, List.mem_append] at member
  rcases member with ((((initial | value) | delimiter) | key) | record) | last
  · simp only [StraightLine.code, List.mem_map] at initial
    obtain ⟨action, _, rfl⟩ := initial
    exact ⟨_, rfl⟩
  · exact FixedWidthCopy.codeWith_native true true 2 n fault instruction value
  · simp only [StraightLine.code, List.mem_map] at delimiter
    obtain ⟨action, _, rfl⟩ := delimiter
    exact ⟨_, rfl⟩
  · exact MarkedBackwardCopy.code_native _ _ _ instruction key
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at record
    subst instruction
    exact ⟨_, rfl⟩
  · exact hTail instruction last

theorem code_native (n κ : Nat) :
    ∀ instruction ∈ code n κ, ∃ native, instruction = .native native := by
  apply codeWithContinuation_native
  intro instruction member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact ⟨_, rfl⟩

/-- The old table is already at its beginning. The source head is just
past the runtime key and value; its arbitrary left prefix is retained. -/
def start {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) : Machine.Configuration where
  inputTape := Tape.ofBits (SimulatorLookup.tableBits table)
  outputTape := { left := (compressionPacket entry.1 ++ entry.2.toList).reverse.map some ++ beforeOutput }

/-- Every cell of the new table and the original source tape survives. -/
def finish {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) : Machine.Configuration where
  pc := haltPc n κ
  inputTape := Tape.ofBits (SimulatorLookup.tableBits (entry :: table))
  outputTape := FixedWidthCopy.backwardFrontier
    ((compressionPacket entry.1 ++ entry.2.toList).map some ++ [none]) beforeOutput
  halted := true

private theorem init_execute {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    StraightLine.execute initActions (start entry table beforeOutput) =
      ({ pc := 2,
         inputTape := { right := (SimulatorLookup.tableBits table).map some },
         outputTape := FixedWidthCopy.backwardFrontier [none]
           (entry.2.toList.reverse.map some ++ (compressionPacket entry.1).reverse.map some ++ beforeOutput) } : Machine.Configuration) := by
  have nonempty : SimulatorLookup.tableBits table ≠ [] := by
    intro empty
    have size := SimulatorLookup.tableBits_length table
    rw [empty] at size
    simp at size
  have moveOutput (cells : List (Option Bool)) :
      ({ left := cells } : Tape).moveLeft = FixedWidthCopy.backwardFrontier [none] cells := by
    cases cells <;> rfl
  unfold start
  generalize ht : SimulatorLookup.tableBits table = tableBits at *
  cases tableBits with
  | nil => contradiction
  | cons bit bits =>
      simp only [initActions, StraightLine.execute, StraightLine.apply,
        Configuration.updateTape, Configuration.advance]
      rw [moveOutput]
      simp [Tape.ofBits, Tape.moveLeft, List.reverse_append, List.map_append, List.append_assoc]


private def valuePrefix : Code := StraightLine.code initActions
private def keyPrefix (n _κ fault : Nat) : Code :=
  valuePrefix ++ FixedWidthCopy.codeWith true true 2 n fault ++ StraightLine.code delimiterActions

private theorem valuePrefix_length : valuePrefix.length = 2 := rfl
private theorem keyPrefix_length (n κ fault : Nat) : (keyPrefix n κ fault).length = keyPc n := by
  simp [keyPrefix, valuePrefix_length, StraightLine.code, delimiterActions, keyPc]; omega

private theorem code_key (n κ fault : Nat) (tail : Code) :
    codeWithContinuation n κ fault tail = keyPrefix n κ fault ++ MarkedBackwardCopy.code (keyPc n) (n + κ + 1) fault ++
      [.native (.write .input true)] ++ tail := by
  simp only [codeWithContinuation, keyPrefix, valuePrefix, List.append_assoc]

private theorem record_instruction (n κ fault : Nat) (tail : Code) :
    (codeWithContinuation n κ fault tail)[keyPc n + 9 * (n + κ + 1)]? = some (.native (.write .input true)) := by
  have size : (keyPrefix n κ fault ++ MarkedBackwardCopy.code (keyPc n) (n + κ + 1) fault).length =
      keyPc n + 9 * (n + κ + 1) := by simp [keyPrefix_length]
  have host : codeWithContinuation n κ fault tail =
      (keyPrefix n κ fault ++ MarkedBackwardCopy.code (keyPc n) (n + κ + 1) fault) ++
        (.native (.write .input true) :: tail) := by simp only [code_key, List.append_assoc, List.singleton_append]
  rw [host, ← size, List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

theorem codeWithContinuation_length (n κ fault : Nat) (tail : Code) :
    (codeWithContinuation n κ fault tail).length = haltPc n κ + tail.length := by
  simp [codeWithContinuation, StraightLine.code, initActions, delimiterActions, haltPc, keyPc]; omega

/-- Every continuation instruction is fetched at its actual absolute address. -/
theorem continuation_instruction (n κ fault : Nat) (tail : Code) (offset : Nat) :
    (codeWithContinuation n κ fault tail)[haltPc n κ + offset]? = tail[offset]? := by
  have size : (keyPrefix n κ fault ++ MarkedBackwardCopy.code (keyPc n) (n + κ + 1) fault ++
      ([.native (.write .input true)] : Code)).length = haltPc n κ := by
    simp [keyPrefix_length, haltPc]; omega
  rw [code_key, ← size, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

private theorem halt_instruction (n κ : Nat) : (code n κ)[haltPc n κ]? = some (.native .halt) := by
  have h := continuation_instruction n κ (faultPc n κ) [.native .halt, .native .halt] 0
  simpa only [Nat.add_zero, List.getElem?_cons_zero, code] using h

/-- Execute the table write and stop immediately before the continuation.
No continuation instruction, including its halt, is executed in this prefix. -/
theorem continuation_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) (fault : Nat) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (codeWithContinuation n κ fault tail) oracle)
      (5 * n + 7 * (n + κ + 1) + 5)
      (NativeCode.frame state trace (start entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace { finish entry table beforeOutput with halted := false }) := by
  let afterValue := StraightLine.code delimiterActions ++
    MarkedBackwardCopy.code (keyPc n) (n + κ + 1) fault ++
    [.native (.write .input true)] ++ tail
  have initial := StraightLine.public_run oracle state trace []
    (FixedWidthCopy.codeWith true true 2 n fault ++ afterValue)
    initActions (start entry table beforeOutput) rfl rfl
  have host : [] ++ StraightLine.code initActions ++
      (FixedWidthCopy.codeWith true true 2 n fault ++ afterValue) = codeWithContinuation n κ fault tail := by
    simp only [codeWithContinuation, afterValue, List.nil_append, List.append_assoc]
  rw [host, init_execute] at initial
  rw [show 5 * n + 7 * (n + κ + 1) + 5 =
    2 + (5 * n + (2 + (7 * (n + κ + 1) + 1))) by omega,
    TimedExecution.eval_add]
  simp only [NativeCode.frame] at ⊢
  change TimedExecution.eval _ 2 _ = _ at initial
  rw [initial, PMF.pure_bind, TimedExecution.eval_add]
  have value := FixedWidthCopy.backward_run oracle state trace valuePrefix afterValue fault
    ((SimulatorLookup.tableBits table).map some) [none]
    ((compressionPacket entry.1).reverse.map some ++ beforeOutput) entry.2.toList.reverse
  simp only [valuePrefix_length, List.length_reverse, Bits.length_toList, List.reverse_reverse] at value
  have valueHost : valuePrefix ++ FixedWidthCopy.codeWith true true 2 n fault ++ afterValue = codeWithContinuation n κ fault tail := by
    simp only [valuePrefix, codeWithContinuation, afterValue, List.append_assoc]
  rw [valueHost] at value
  simp only [List.append_assoc] at ⊢
  rw [value, PMF.pure_bind]
  let beforeDelimiter := valuePrefix ++ FixedWidthCopy.codeWith true true 2 n fault
  let afterDelimiter := MarkedBackwardCopy.code (keyPc n) (n + κ + 1) fault ++
    [.native (.write .input true)] ++ tail
  have delimiter := StraightLine.public_run oracle state trace beforeDelimiter afterDelimiter delimiterActions
    { pc := 2 + 7 * n, inputTape := { right := entry.2.toList.map some ++ (SimulatorLookup.tableBits table).map some }, outputTape := FixedWidthCopy.backwardFrontier (entry.2.toList.map some ++ [none]) ((compressionPacket entry.1).reverse.map some ++ beforeOutput) }
    (by simp [beforeDelimiter, valuePrefix_length]) rfl
  have delimiterHost : beforeDelimiter ++ StraightLine.code delimiterActions ++ afterDelimiter = codeWithContinuation n κ fault tail := by
    simp only [beforeDelimiter, afterDelimiter, valuePrefix, codeWithContinuation, List.append_assoc]
  rw [delimiterHost] at delimiter
  rw [TimedExecution.eval_add]
  change TimedExecution.eval _ 2 _ = _ at delimiter
  rw [delimiter, PMF.pure_bind]
  simp only [delimiterActions, StraightLine.execute, StraightLine.apply,
    Configuration.updateTape, Configuration.advance, Tape.write, Tape.moveLeft]
  have key := MarkedBackwardCopy.run oracle state trace (keyPrefix n κ fault)
    ([.native (.write .input true)] ++ tail) fault
    (some false :: entry.2.toList.map some ++ (SimulatorLookup.tableBits table).map some)
    (entry.2.toList.map some ++ [none]) beforeOutput (compressionPacket entry.1).reverse
  simp only [keyPrefix_length, List.length_reverse, compressionPacket_length, List.reverse_reverse] at key
  have keyHost := code_key n κ fault tail
  simp only [List.append_assoc] at keyHost key
  rw [← keyHost] at key
  rw [show 2 + 7 * n + 1 + 1 = keyPc n by unfold keyPc; omega]
  rw [TimedExecution.eval_add]
  simp only [List.cons_append] at key ⊢
  rw [key, PMF.pure_bind]
  have record := record_instruction n κ fault tail
  have layout : true :: DelimitedTapeComparison.marked (compressionPacket entry.1) ++
      false :: entry.2.toList ++ SimulatorLookup.tableBits table = SimulatorLookup.tableBits (entry :: table) := by
    rw [SimulatorLookup.tableBits_cons]
    simp [SimulatorLookup.entryBits, DelimitedTapeComparison.delimit_eq_marked, List.append_assoc]
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, record,
      Machine.Instruction.next, Configuration.advance, Configuration.updateTape, Tape.write,
      finish, SimulatorLookup.tableBits_cons, SimulatorLookup.entryBits,
      DelimitedTapeComparison.delimit_eq_marked, Tape.ofBits, haltPc,
      List.map_append, List.append_assoc]

/-- Exact adjacent execution horizons, including the final actual halt.
All table cells are written by ordinary one-cell instructions. -/
theorem stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (5 * n + 7 * (n + κ + 1) + 5 + halt.toNat)
      (NativeCode.frame state trace (start entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace { finish entry table beforeOutput with halted := halt }) := by
  rw [TimedExecution.eval_add]
  have leading := continuation_run oracle state trace entry table beforeOutput (faultPc n κ)
    [.native .halt, .native .halt]
  change TimedExecution.eval (Reification.timedStep (code n κ) oracle)
    (5 * n + 7 * (n + κ + 1) + 5) _ = _ at leading
  rw [leading, PMF.pure_bind]
  have stopped := halt_instruction n κ
  cases halt <;>
    simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, NativeCode.frame,
      Reification.perform, Reification.action, transition, finish, stopped,
      Machine.Instruction.next]

/-- The existing native rewind retains one explicit outer blank. The
first actual left move consumes it; no normalization is performed. -/
def startAfterRewind {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) : Machine.Configuration :=
  { start entry table beforeOutput with inputTape := { Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] } }

theorem continuation_run_after_rewind {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) (fault : Nat) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (codeWithContinuation n κ fault tail) oracle)
      (5 * n + 7 * (n + κ + 1) + 5)
      (NativeCode.frame state trace (startAfterRewind entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace { finish entry table beforeOutput with halted := false }) := by
  have sameStep : Reification.timedStep (codeWithContinuation n κ fault tail) oracle
      (NativeCode.frame state trace (startAfterRewind entry table beforeOutput)) =
      Reification.timedStep (codeWithContinuation n κ fault tail) oracle
        (NativeCode.frame state trace (start entry table beforeOutput)) := by
    cases bits : SimulatorLookup.tableBits table <;>
    simp [bits, Reification.timedStep, Reification.terminal, NativeCode.frame, startAfterRewind, start,
      codeWithContinuation, StraightLine.code, StraightLine.instruction, initActions, Reification.perform,
      Reification.action, transition, Machine.Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.moveLeft, Tape.ofBits]
  have transport (fuel : Nat) : TimedExecution.eval (Reification.timedStep (codeWithContinuation n κ fault tail) oracle) (fuel + 1)
      (NativeCode.frame state trace (startAfterRewind entry table beforeOutput)) =
      TimedExecution.eval (Reification.timedStep (codeWithContinuation n κ fault tail) oracle) (fuel + 1)
        (NativeCode.frame state trace (start entry table beforeOutput)) := by
    simp only [TimedExecution.eval, sameStep]
  have positive : 0 < 5 * n + 7 * (n + κ + 1) + 5 := by omega
  rw [show 5 * n + 7 * (n + κ + 1) + 5 =
    (5 * n + 7 * (n + κ + 1) + 5 - 1) + 1 by omega, transport,
    Nat.sub_add_cancel positive, continuation_run]

theorem stage_run_after_rewind {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (5 * n + 7 * (n + κ + 1) + 5 + halt.toNat)
      (NativeCode.frame state trace (startAfterRewind entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace { finish entry table beforeOutput with halted := halt }) := by
  rw [TimedExecution.eval_add]
  have leading := continuation_run_after_rewind oracle state trace entry table beforeOutput (faultPc n κ)
    [.native .halt, .native .halt]
  change TimedExecution.eval (Reification.timedStep (code n κ) oracle)
    (5 * n + 7 * (n + κ + 1) + 5) _ = _ at leading
  rw [leading, PMF.pure_bind]
  have stopped := halt_instruction n κ
  cases halt <;>
    simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, NativeCode.frame,
      Reification.perform, Reification.action, transition, finish, stopped, Machine.Instruction.next]

/-- The exact transition count from the stated physical entry layout. -/
def steps (n κ : Nat) : Nat := 5 * n + 7 * (n + κ + 1) + 6

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps n κ)
      (NativeCode.frame state trace (start entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (finish entry table beforeOutput)) := by
  simpa [steps, finish] using stage_run oracle state trace entry table beforeOutput true

/-- Actual first halt, jointly with every table/source cell, external state
and previous transcript. No external capability is called by this code. -/
theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control) (steps n κ)
      (NativeCode.frame state trace (start entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (finish entry table beforeOutput), steps n κ) := by
  have adjacent : steps n κ - 1 + 1 = steps n κ := by unfold steps; omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (start entry table beforeOutput)) (steps n κ - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := stage_run oracle state trace entry table beforeOutput false
        have size : steps n κ - 1 = 5 * n + 7 * (n + κ + 1) + 5 := by unfold steps; omega
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [size, law, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
    (by intro frame support
        rw [adjacent, run, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
  simpa only [adjacent, run, PMF.pure_map] using h

structure Input (State : Type*) (n κ : Nat) where
  state : State
  trace : List (List Bool × List Bool)
  entry : CompressionInput (Bits κ) (Bits n) × Bits n
  table : CompressionTable (Bits κ) (Bits n)
  beforeOutput : List (Option Bool)

/-- Reuse Foundation's composable execution certificate with the full
physical frame as output. Tape preparation remains an entry obligation. -/
noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (Reification.timedStep (code n κ) oracle) (Input State n κ) (Configuration State) :=
  TimedExecution.Procedure.ofFixed _
    (fun input => NativeCode.frame input.state input.trace (start input.entry input.table input.beforeOutput))
    (fun _ output => output)
    (fun input => PMF.pure (NativeCode.frame input.state input.trace (finish input.entry input.table input.beforeOutput)))
    (fun _ => steps n κ)
    (fun input => by rw [run, PMF.pure_map])

theorem procedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (procedure n κ oracle) := by
  apply Procedure.operational_ofFixed

theorem procedure_first_joint {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : Input State n κ) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control)
      ((procedure n κ oracle).budget input) ((procedure n κ oracle).entry input) =
      (procedure n κ oracle).costed input := by
  change runToBoundary _ _ (steps n κ)
    (NativeCode.frame input.state input.trace (start input.entry input.table input.beforeOutput)) = _
  rw [first_joint]
  simp only [procedure, TimedExecution.Procedure.ofFixed, PMF.pure_map]

end Foundation.Hash.Native.SimulatorRemember
