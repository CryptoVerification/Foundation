import Foundation.Constructions.Hash.NativeSimulatorReconstruct
import Foundation.Crypto.Semantics.Oracle.UnaryCounterTransfer

/-! Count physical compression-table records into a unary output field. The
same finite loop reads each original list marker and crosses exactly one
fixed-width record; host-computed table length is used only in the proof. -/
namespace Foundation.Hash.Native.SimulatorTableCount
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def width (n κ : Nat) : Nat := 3 * n + 2 * κ + 4
def prelude (n κ : Nat) : Code :=
  [.native (.branch .input (width n κ + 4) (width n κ + 4) 1),
   .native (.write .output true), .native (.moveLeft .output)]
def body (n κ : Nat) : Code :=
  prelude n κ ++ StraightLine.code (List.replicate (width n κ) (.right .input)) ++ [.native (.jump 0)]
def code (n κ : Nat) (tail : Code) : Code := CodeRelocation.host (body n κ) tail

theorem body_length (n κ : Nat) : (body n κ).length = width n κ + 4 := by
  simp [body, prelude, StraightLine.code]

theorem entry_length (entry : CompressionInput (Bits κ) (Bits n) × Bits n) :
    (SimulatorLookup.entryBits entry).length = width n κ := by
  simp [SimulatorLookup.entryBits, compressionPacket, FiniteBitEncoding.delimit_length, width]
  omega

theorem prelude_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code)
    (left cells right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ tail) oracle) 3
      (NativeCode.frame state trace { inputTape := FixedWidthCopy.frontier left (some true :: cells), outputTape := { right := right } }) =
      PMF.pure (NativeCode.frame state trace { pc := 3, inputTape := FixedWidthCopy.frontier left (some true :: cells), outputTape := { right := some true :: right } }) := by
  simp [code, body, prelude, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
    Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
    transition, Machine.Instruction.next, Machine.Configuration.advance,
    Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.frontier,
    ResponseLoading.fromCells, Tape.moveLeft, Tape.write]

theorem record_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code)
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (left rest right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ tail) oracle) (width n κ + 4)
      (NativeCode.frame state trace { inputTape := FixedWidthCopy.frontier left ((SimulatorLookup.entryBits entry).map some ++ rest), outputTape := { right := right } }) =
      PMF.pure (NativeCode.frame state trace
        { inputTape := FixedWidthCopy.frontier ((SimulatorLookup.entryBits entry).reverse.map some ++ left) rest, outputTape := { right := some true :: right } }) := by
  let actions := List.replicate (width n κ) (StraightLine.Action.right .input)
  have hs := StraightLine.public_run oracle state trace (prelude n κ)
    ([.native (.jump 0)] ++ tail.map (CodeRelocation.instruction (body n κ).length)) actions
    { pc := 3, inputTape := FixedWidthCopy.frontier left ((SimulatorLookup.entryBits entry).map some ++ rest), outputTape := { right := some true :: right } }
    rfl rfl
  have hm := FixedWidthCopy.advance_input (SimulatorLookup.entryBits entry) left rest
    ({ pc := 3, outputTape := { right := some true :: right } } : Machine.Configuration)
  rw [entry_length] at hm
  rw [show StraightLine.execute actions _ = _ from hm] at hs
  have hform : prelude n κ ++ StraightLine.code actions ++
      ([.native (.jump 0)] ++ tail.map (CodeRelocation.instruction (body n κ).length)) = code n κ tail := by
    simp [code, body, actions, CodeRelocation.host, List.append_assoc]
  rw [hform] at hs
  simp only [actions, List.length_replicate] at hs
  have hp : TimedExecution.eval (Reification.timedStep (code n κ tail) oracle) 3
      (NativeCode.frame state trace { inputTape := FixedWidthCopy.frontier left ((SimulatorLookup.entryBits entry).map some ++ rest), outputTape := { right := right } }) =
      PMF.pure (NativeCode.frame state trace { pc := 3, inputTape := FixedWidthCopy.frontier left ((SimulatorLookup.entryBits entry).map some ++ rest), outputTape := { right := some true :: right } }) := by
    simpa only [SimulatorLookup.entryBits, List.map_cons, List.cons_append] using
      prelude_run (n := n) (κ := κ) oracle state trace tail left _ right
  have fetch : (code n κ tail)[3 + width n κ]? = some (.native (.jump 0)) := by
    have hl : (prelude n κ ++ StraightLine.code actions).length = 3 + width n κ := by
      simp [prelude, actions, StraightLine.code]
      omega
    rw [← hform, ← hl, List.getElem?_append_right (by omega), Nat.sub_self]; rfl
  rw [show width n κ + 4 = 3 + (width n κ + 1) from by omega, TimedExecution.eval_add,
    hp, PMF.pure_bind, TimedExecution.eval_add]
  simp only [NativeCode.frame]
  rw [hs, PMF.pure_bind]
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
    Reification.perform, Reification.action, transition, Machine.Instruction.next, fetch]

theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code)
    (table : CompressionTable (Bits κ) (Bits n)) (left right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ tail) oracle)
      (table.length * (width n κ + 4) + 1)
      (NativeCode.frame state trace { inputTape := FixedWidthCopy.frontier left ((SimulatorLookup.tableBits table).map some), outputTape := { right := right } }) =
      PMF.pure (CodeRelocation.frame (body n κ).length
        (NativeCode.frame state trace
          { inputTape := { left := (table.flatMap SimulatorLookup.entryBits).reverse.map some ++ left, current := some false },
            outputTape := { right := List.replicate table.length (some true) ++ right } })) := by
  induction table generalizing left right with
  | nil =>
      simp [SimulatorLookup.tableBits, code, body, prelude, StraightLine.code, CodeRelocation.host,
        NativeCode.frame, TimedExecution.eval, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, Machine.Instruction.next,
        Machine.Configuration.tape, FixedWidthCopy.frontier, ResponseLoading.fromCells,
        CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]
  | cons entry rest ih =>
      rw [show (entry :: rest).length * (width n κ + 4) + 1 = (width n κ + 4) + (rest.length * (width n κ + 4) + 1) from by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega,
        TimedExecution.eval_add]
      simp only [SimulatorLookup.tableBits_cons, List.map_append]
      rw [record_run, PMF.pure_bind, ih]
      simp [List.flatMap_cons, List.reverse_append, List.map_append, List.append_assoc,
        List.replicate_succ, UnaryFuel.replicate_push]

theorem body_native (n κ : Nat) : ∀ op ∈ body n κ, ∃ native, op = .native native := by
  intro op hm
  simp only [body, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · simp only [prelude, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · obtain ⟨action, _, rfl⟩ := List.mem_map.mp hm; exact ⟨_, rfl⟩
  · exact ⟨_, by simpa using hm⟩

end Foundation.Hash.Native.SimulatorTableCount
