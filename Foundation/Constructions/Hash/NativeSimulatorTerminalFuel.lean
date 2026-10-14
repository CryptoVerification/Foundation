import Foundation.Constructions.Hash.NativeSimulatorFuelPrepare
import Foundation.Constructions.Hash.NativeSimulatorTerminalGuard

/-! Connect a terminal-guard success to runtime fuel initialization. The
original packet is retained for the subsequent protected-key save; no message
suffix is written over that packet in this stage. -/
namespace Foundation.Hash.Native.SimulatorTerminalFuel
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def moveActions (n : Nat) : List StraightLine.Action := List.replicate (n + 1) (.left .output)
def moveCode (n : Nat) : Code := StraightLine.code (moveActions n)
def body (n κ : Nat) (tail : Code) : Code := CodeRelocation.host (moveCode n) (SimulatorFuelPrepare.code n κ tail)
def code (terminal : Bits κ) (n : Nat) (tail rejected : Code) : Code :=
  SimulatorTerminalGuard.code terminal (body n κ tail) rejected
def guardPrefix (terminal : Bits κ) (accepted : Code) : Code :=
  CodeRelocation.host [.native (.moveLeft .output)]
    (SimulatorTerminalCheck.compareCode accepted.length [] (SimulatorTerminalGuard.expected terminal))

def queryCells (target : Bits n) (terminal : Bits κ) : List (Option Bool) :=
  (compressionPacket (target, (true, terminal))).map some ++ [some false, none]
def flagStart (target : Bits n) (terminal : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier [none] ((SimulatorLookup.tableBits table).map some),
    outputTape := { left := (compressionPacket (target, (true, terminal))).reverse.map some, current := some false, right := [none] } }
def acceptedStart (target : Bits n) (terminal : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) : Machine.Configuration :=
  { inputTape := (flagStart target terminal table).inputTape,
    outputTape := FixedWidthCopy.backwardFrontier ((true :: terminal.toList).map some ++ [some false, none]) (target.toList.reverse.map some) }

theorem guard_host (terminal : Bits κ) (accepted rejected : Code) :
    SimulatorTerminalGuard.code terminal accepted rejected =
      CodeRelocation.host (guardPrefix terminal accepted) (CodeRelocation.host accepted rejected) := by
  rw [SimulatorTerminalGuard.code, SimulatorTerminalGuard.compareCode_link, ← CodeRelocation.host_assoc]; rfl

theorem guardPrefix_length (terminal : Bits κ) (accepted : Code) :
    (guardPrefix terminal accepted).length = 1 + 2 * (κ + 1) := by
  simp [guardPrefix, CodeRelocation.code_length, SimulatorTerminalCheck.compareCode_length,
    SimulatorTerminalGuard.expected_length]

theorem move_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (target : Bits n) (terminal : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (moveCode n) tail) oracle) (n + 1)
      (NativeCode.frame state trace (acceptedStart target terminal table)) =
      PMF.pure (CodeRelocation.frame (moveCode n).length
        (NativeCode.frame state trace (SimulatorFuelPrepare.start table (queryCells target terminal)))) := by
  have hm := BackwardFieldCopy.advance_output (target.toList.reverse.map some)
    ((true :: terminal.toList).map some ++ [some false, none]) []
    ({ inputTape := (flagStart target terminal table).inputTape } : Machine.Configuration)
  simp only [List.length_map, List.length_reverse, Bits.length_toList, List.append_nil] at hm
  have hs := StraightLine.public_run oracle state trace [] (tail.map (CodeRelocation.instruction (moveCode n).length))
    (moveActions n) (acceptedStart target terminal table) rfl rfl
  have ha : moveActions n = List.replicate n (.left .output) ++ [.left .output] := by
    exact List.replicate_succ'
  change StraightLine.execute (List.replicate n (.left .output)) (acceptedStart target terminal table) = _ at hm
  have he : StraightLine.execute (moveActions n) (acceptedStart target terminal table) =
      { pc := n + 1, inputTape := (SimulatorFuelPrepare.start table (queryCells target terminal)).inputTape,
        outputTape := (SimulatorFuelPrepare.start table (queryCells target terminal)).outputTape } := by
    rw [ha, StraightLine.execute_append, hm]
    simp [StraightLine.execute, StraightLine.apply, Machine.Configuration.advance,
      Machine.Configuration.updateTape, FixedWidthCopy.backwardFrontier, Tape.moveLeft,
      queryCells, compressionPacket, SimulatorFuelPrepare.start, flagStart,
      ← List.map_reverse, List.reverse_reverse, List.append_assoc]
  rw [he] at hs
  simpa [moveCode, moveActions, CodeRelocation.host, CodeRelocation.frame, CodeRelocation.control,
    NativeCode.frame, Machine.Configuration.rebasePc, StraightLine.execute, StraightLine.apply,
    Machine.Configuration.advance, Machine.Configuration.updateTape, FixedWidthCopy.backwardFrontier,
    Tape.moveLeft, queryCells, compressionPacket, SimulatorFuelPrepare.start, flagStart,
    ← List.map_reverse, List.reverse_reverse, List.append_assoc, StraightLine.code] using hs

theorem body_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (target : Bits n) (terminal : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) :
    TimedExecution.eval (Reification.timedStep (body n κ tail) oracle)
      (n + 1 + SimulatorFuelPrepare.steps table)
      (NativeCode.frame state trace (acceptedStart target terminal table)) =
      PMF.pure (CodeRelocation.frame (body n κ []).length
        (NativeCode.frame state trace (SimulatorFuelPrepare.finish table (queryCells target terminal)))) := by
  have h := SimulatorPredecessorExtract.seq_run oracle (moveCode n) (SimulatorFuelPrepare.code n κ tail) _ _ _ _ _
    (move_run oracle state trace _ target terminal table)
    (SimulatorFuelPrepare.run oracle state trace tail table (queryCells target terminal))
  simpa only [body, SimulatorFuelPrepare.steps, CodeRelocation.code_length, CodeRelocation.frame,
    CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc, Nat.add_zero, Nat.add_assoc] using h

/-- A fixed-terminal acceptance creates exactly table.length units of runtime
fuel and returns the complete original query at its correctly relocated tail. -/
theorem accepted_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail rejected : Code) (target : Bits n) (terminal : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) :
    TimedExecution.eval (Reification.timedStep (code terminal n tail rejected) oracle)
      ((1 + 2 * (κ + 1)) + (n + 1 + SimulatorFuelPrepare.steps table))
      (NativeCode.frame state trace (flagStart target terminal table)) =
      PMF.pure (CodeRelocation.frame ((guardPrefix terminal (body n κ tail)).length + (body n κ []).length)
        (NativeCode.frame state trace (SimulatorFuelPrepare.finish table (queryCells target terminal)))) := by
  have hg := SimulatorTerminalGuard.accepted_run oracle state trace terminal (body n κ tail) rejected
    (flagStart target terminal table).inputTape (some false) (target, (true, terminal)) [] [none] ⟨rfl, rfl⟩
  have hg' : TimedExecution.eval (Reification.timedStep (code terminal n tail rejected) oracle) (1 + 2 * (κ + 1))
      (NativeCode.frame state trace (flagStart target terminal table)) =
      PMF.pure (CodeRelocation.frame (guardPrefix terminal (body n κ tail)).length
        (NativeCode.frame state trace (acceptedStart target terminal table))) := by
    simpa [code, NativeCode.frame, flagStart, acceptedStart, guardPrefix_length,
      CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
      SimulatorTerminalCheck.seekFrontier, FixedWidthCopy.backwardFrontier,
      SimulatorTerminalGuard.expected, List.reverse_append, List.reverse_cons, List.map_append,
      List.append_assoc] using hg
  have hb := body_run oracle state trace tail target terminal table
  have ha := CodePrefixExecution.append_active (body n κ tail)
    (rejected.map (CodeRelocation.instruction (body n κ tail).length)) oracle
    (n + 1 + SimulatorFuelPrepare.steps table)
    (NativeCode.frame state trace (acceptedStart target terminal table))
    (by intro out hm; rw [hb, PMF.mem_support_pure_iff] at hm; subst out; rfl)
  have hb' : TimedExecution.eval (Reification.timedStep (CodeRelocation.host (body n κ tail) rejected) oracle)
      (n + 1 + SimulatorFuelPrepare.steps table) (NativeCode.frame state trace (acceptedStart target terminal table)) =
      PMF.pure (CodeRelocation.frame (body n κ []).length (NativeCode.frame state trace (SimulatorFuelPrepare.finish table (queryCells target terminal)))) := by
    rw [CodeRelocation.host, ha, hb]
  rw [code, guard_host] at hg' ⊢
  have h := SimulatorPredecessorExtract.seq_run oracle (guardPrefix terminal (body n κ tail)) _ _ _ _ _ _ hg' hb'
  simpa only [CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc,
    Nat.add_zero, Nat.add_assoc] using h

theorem key_preserved (target : Bits n) (terminal : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) :
    (SimulatorFuelPrepare.finish table (queryCells target terminal)).outputTape.bits =
      compressionPacket (target, (true, terminal)) ++ [false] := by
  have hnonempty : queryCells target terminal ≠ [] := by
    simp [queryCells]
  have hf (left cells : List (Option Bool)) (hn : cells ≠ []) :
      (FixedWidthCopy.frontier left cells).bits = left.reverse.filterMap id ++ cells.filterMap id := by
    cases cells <;> simp_all [FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.bits]
  rw [SimulatorFuelPrepare.finish, hf _ _ hnonempty]
  simp [queryCells, List.filterMap_map]

theorem code_length (terminal : Bits κ) (n : Nat) (tail rejected : Code) :
    (code terminal n tail rejected).length = 4 * n + 4 * κ + 31 + tail.length + rejected.length := by
  rw [code, SimulatorTerminalGuard.code_length]
  simp [body, CodeRelocation.code_length, moveCode, moveActions, StraightLine.code, SimulatorFuelPrepare.code_length]
  omega

theorem code_native (terminal : Bits κ) (n : Nat) (tail rejected : Code)
    (ht : ∀ op ∈ tail, ∃ native, op = .native native)
    (hr : ∀ op ∈ rejected, ∃ native, op = .native native) :
    ∀ op ∈ code terminal n tail rejected, ∃ native, op = .native native := by
  apply SimulatorTerminalGuard.code_native _ _ _ _ hr
  apply CodeRelocation.host_native
  · intro op hm; obtain ⟨action, _, rfl⟩ := List.mem_map.mp hm; exact ⟨_, rfl⟩
  · exact SimulatorFuelPrepare.code_native _ _ _ ht

theorem counter_ready (target : Bits n) (terminal : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) :
    (SimulatorFuelPrepare.finish table (queryCells target terminal)).inputTape =
      UnaryFuel.tape table.length 0 ((SimulatorLookup.tableBits table).map some) := rfl

def steps (table : CompressionTable (Bits κ) (Bits n)) : Nat :=
  (1 + 2 * (κ + 1)) + (n + 1 + SimulatorFuelPrepare.steps table)

theorem steps_eq (table : CompressionTable (Bits κ) (Bits n)) :
    steps table = table.length * (12 * n + 8 * κ + 29) + n + 2 * κ + 18 := by
  unfold steps SimulatorFuelPrepare.steps SimulatorTableCount.width
  ring

theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (target : Bits n) (terminal : Bits κ) (table : CompressionTable (Bits κ) (Bits n)) (elapsed : Nat)
    (within : elapsed ≤ steps table) (out : Configuration State)
    (supported : out ∈ (TimedExecution.eval (Reification.timedStep (code terminal n [] [.native .halt]) oracle) elapsed
      (NativeCode.frame state trace (flagStart target terminal table))).support) :
    ((NativeCode.fullEncoding E).encode (code terminal n [] [.native .halt], out)).length ≤
      NativeCode.storageBound (code terminal n [] [.native .halt])
        (NativePacketComponent.Resources.frameSize stateSize (NativeCode.frame state trace (flagStart target terminal table))) (steps table) :=
  NativeCode.encoded_peak E stateSize hState oracle state trace _
    (code_native _ _ _ _ (by simp) (by intro op hm; exact ⟨_, by simpa using hm⟩)) _ _ elapsed within out supported

end Foundation.Hash.Native.SimulatorTerminalFuel
