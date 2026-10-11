import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy
import Foundation.Crypto.Semantics.Oracle.NativeCode
import Foundation.Crypto.Semantics.Machine.NativeFixedComponent

/-! Compare a raw candidate field against an equally wide raw query followed
by a blank. Only the query needs a delimiter: a private table's response field
can be immediately followed by the next record marker. Both strings and the
complete candidate suffix are retained. The query delimiter becomes the result.
This is a fixed 14-instruction native loop, independent of the field width. -/
namespace CryptoOracle.Interactive.RawTapeEquality
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def program : Machine.Program :=
  [.branch .output 12 1 5,
   .branch .input 6 2 6,
   .moveRight .input, .moveRight .output, .jump 0,
   .branch .input 6 6 2,
   .branch .output 10 7 7,
   .moveRight .input, .moveRight .output, .jump 6,
   .write .output false, .halt,
   .write .output true, .halt]

def code : Code := NativeCode.code program

theorem program_length : program.length = 14 := rfl

theorem code_native : ∀ i ∈ code, ∃ op, i = .native op := by
  intro i hi
  simp only [code, NativeCode.code, List.mem_map] at hi
  obtain ⟨op, _, h⟩ := hi
  exact ⟨op, h.symm⟩

theorem agree_iteration (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (leftInput leftOutput inputCells outputCells : List (Option Bool))
    (bit : Bool) :
    TimedExecution.eval (Reification.timedStep code oracle) 5
      (⟨state, .running { inputTape := FixedWidthCopy.frontier leftInput (some bit :: inputCells), outputTape := FixedWidthCopy.frontier leftOutput (some bit :: outputCells) }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { inputTape := FixedWidthCopy.frontier (some bit :: leftInput) inputCells, outputTape := FixedWidthCopy.frontier (some bit :: leftOutput) outputCells }, trace⟩ := by
  cases bit <;> cases inputCells <;> cases outputCells <;>
    simp [code, NativeCode.code, program, TimedExecution.eval, Reification.timedStep,
      Reification.terminal, Reification.perform, Reification.action, transition,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.moveRight]

theorem differ_step (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input output : Tape) (a b : Bool)
    (hi : input.current = some a) (ho : output.current = some b) (hne : a ≠ b) :
    TimedExecution.eval (Reification.timedStep code oracle) 2
      (⟨state, .running { inputTape := input, outputTape := output }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 6, inputTape := input, outputTape := output }, trace⟩ := by
  cases a <;> cases b <;>
    simp_all [code, NativeCode.code, program, TimedExecution.eval, Reification.timedStep,
      Reification.terminal, Reification.perform, Reification.action, transition,
      Machine.Instruction.next, Machine.Configuration.tape]

theorem skip_iteration (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (leftInput leftOutput inputCells outputCells : List (Option Bool))
    (a b : Bool) :
    TimedExecution.eval (Reification.timedStep code oracle) 4
      (⟨state, .running { pc := 6, inputTape := FixedWidthCopy.frontier leftInput (some a :: inputCells), outputTape := FixedWidthCopy.frontier leftOutput (some b :: outputCells) }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 6, inputTape := FixedWidthCopy.frontier (some a :: leftInput) inputCells, outputTape := FixedWidthCopy.frontier (some b :: leftOutput) outputCells }, trace⟩ := by
  cases b <;> cases inputCells <;> cases outputCells <;>
    simp [code, NativeCode.code, program, TimedExecution.eval, Reification.timedStep,
      Reification.terminal, Reification.perform, Reification.action, transition,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.moveRight]

def finish (candidate query : List Bool) (leftInput leftOutput inputTail outputTail : List (Option Bool))
    (equal : Bool) : Machine.Configuration :=
  { pc := if equal then 13 else 11, halted := true,
    inputTape := FixedWidthCopy.frontier (candidate.reverse.map some ++ leftInput) inputTail,
    outputTape := { left := query.reverse.map some ++ leftOutput, current := some equal, right := outputTail } }

/-- Once a mismatch was seen, advance both heads to the field boundary. -/
theorem skip_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (candidate query : List Bool) (width : candidate.length = query.length)
    (leftInput leftOutput inputTail outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) (4 * query.length + 3)
      (⟨state, .running { pc := 6, inputTape := FixedWidthCopy.frontier leftInput (candidate.map some ++ inputTail), outputTape := FixedWidthCopy.frontier leftOutput (query.map some ++ none :: outputTail) }, trace⟩ : Configuration State) =
      PMF.pure (NativeCode.frame state trace (finish candidate query leftInput leftOutput inputTail outputTail false)) := by
  induction query generalizing candidate leftInput leftOutput with
  | nil =>
      cases candidate with
      | cons a rest => simp at width
      | nil =>
          simp [code, NativeCode.code, program, TimedExecution.eval, Reification.timedStep,
            Reification.terminal, Reification.perform, Reification.action, transition,
            Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
            Machine.Configuration.advance, finish, NativeCode.frame, FixedWidthCopy.frontier,
            ResponseLoading.fromCells, Tape.write]
  | cons b rest ih =>
      cases candidate with
      | nil => simp at width
      | cons a remaining =>
          have hw : remaining.length = rest.length := by simpa using width
          rw [show 4 * (b :: rest).length + 3 = 4 + (4 * rest.length + 3) from by simp; omega,
            TimedExecution.eval_add]
          simp only [List.map_cons, List.cons_append]
          rw [skip_iteration, PMF.pure_bind, ih remaining hw (some a :: leftInput) (some b :: leftOutput)]
          simp [finish, NativeCode.frame, List.reverse_cons, List.map_append, List.append_assoc]

/-- Actual execution length, distinguishing early mismatch from full agreement. -/
def steps : List Bool → List Bool → Nat
  | [], _ => 3
  | _, [] => 3
  | a :: candidate, b :: query =>
      if a = b then 5 + steps candidate query else 2 + (4 * (b :: query).length + 3)

/-- Exact complete execution and retained physical table/query layout. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (candidate query : List Bool) (width : candidate.length = query.length)
    (leftInput leftOutput inputTail outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) (steps candidate query)
      (⟨state, .running { inputTape := FixedWidthCopy.frontier leftInput (candidate.map some ++ inputTail), outputTape := FixedWidthCopy.frontier leftOutput (query.map some ++ none :: outputTail) }, trace⟩ : Configuration State) =
      PMF.pure (NativeCode.frame state trace (finish candidate query leftInput leftOutput inputTail outputTail (decide (candidate = query)))) := by
  induction candidate generalizing query leftInput leftOutput with
  | nil =>
      cases query with
      | cons b rest => simp at width
      | nil =>
          simp [steps, code, NativeCode.code, program, TimedExecution.eval, Reification.timedStep,
            Reification.terminal, Reification.perform, Reification.action, transition,
            Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
            Machine.Configuration.advance, finish, NativeCode.frame, FixedWidthCopy.frontier,
            ResponseLoading.fromCells, Tape.write]
  | cons a rest ih =>
      cases query with
      | nil => simp at width
      | cons b remaining =>
          have hw : rest.length = remaining.length := by simpa using width
          by_cases hab : a = b
          · subst b
            rw [steps, if_pos rfl, TimedExecution.eval_add]
            simp only [List.map_cons, List.cons_append]
            rw [agree_iteration, PMF.pure_bind, ih remaining hw (some a :: leftInput) (some a :: leftOutput)]
            simp [finish, NativeCode.frame, List.reverse_cons, List.map_append, List.append_assoc]
          · rw [steps, if_neg hab, TimedExecution.eval_add]
            rw [differ_step oracle state trace _ _ a b rfl rfl hab, PMF.pure_bind,
              skip_run oracle state trace (a :: rest) (b :: remaining) width]
            simp [hab]

theorem steps_self (bits : List Bool) : steps bits bits = 5 * bits.length + 3 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [steps, ih]; omega

theorem steps_bound (candidate query : List Bool) (width : candidate.length = query.length) :
    steps candidate query ≤ 5 * query.length + 5 := by
  induction candidate generalizing query with
  | nil => cases query <;> simp_all [steps]
  | cons a rest ih =>
      cases query with
      | nil => simp at width
      | cons b remaining =>
          have hw : rest.length = remaining.length := by simpa using width
          have hb := ih remaining hw
          simp only [steps]
          split <;> simp only [List.length_cons] <;> omega

structure Input where
  candidate : List Bool
  query : List Bool
  width : candidate.length = query.length
  leftInput : List (Option Bool) := []
  leftOutput : List (Option Bool) := []
  inputTail : List (Option Bool) := []
  outputTail : List (Option Bool) := []

def start (input : Input) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier input.leftInput (input.candidate.map some ++ input.inputTail),
    outputTape := FixedWidthCopy.frontier input.leftOutput (input.query.map some ++ none :: input.outputTail) }

def result (input : Input) : Machine.Configuration :=
  finish input.candidate input.query input.leftInput input.leftOutput input.inputTail input.outputTail
    (decide (input.candidate = input.query))

theorem closed : program.ControlClosed := by decide

private def unframe (c : Configuration Unit) : Machine.Configuration :=
  match c.control with
  | .running machine => machine
  | _ => {}

/-- Transfer the proved interactive run back to the original native semantics. -/
theorem native_run (input : Input) :
    Machine.evalConfigWithin program (start input) (steps input.candidate input.query) =
      PMF.pure (result input) := by
  let oracle : BitOracle Unit := fun _ _ => PMF.pure ((), [])
  have h := run oracle () [] input.candidate input.query input.width
    input.leftInput input.leftOutput input.inputTail input.outputTail
  change TimedExecution.eval (Reification.timedStep (NativeCode.code program) oracle)
    (steps input.candidate input.query) (NativeCode.frame () [] (start input)) =
    PMF.pure (NativeCode.frame () [] (result input)) at h
  rw [NativeCode.closed_eval program oracle (Machine.Program.controlClosed_step closed)
    () [] (steps input.candidate input.query) (start input) (Or.inr (by change 0 < 14; decide))] at h
  have hp := congrArg (PMF.map unframe) h
  simp only [PMF.map_comp, PMF.pure_map, Function.comp_def, NativeCode.frame, unframe] at hp
  change PMF.map id (Machine.evalConfigWithin program (start input) (steps input.candidate input.query)) =
    PMF.pure (result input) at hp
  rw [PMF.map_id] at hp
  exact hp

theorem result_status (input : Input) :
    (result input).outputTape.current = some (decide (input.candidate = input.query)) := rfl

/-- A genuine native component, ready for charged subroutine linking. -/
noncomputable def component : NativeComponent Input Machine.Configuration :=
  NativeComponent.ofFixed program start (fun _ out => out) (fun input => PMF.pure (result input))
    (fun input => steps input.candidate input.query)
    (fun input => by simpa only [PMF.pure_map] using native_run input)
    closed (fun _ => by change 0 < 14; decide) (fun _ => rfl)
    (by intro input out h; rw [PMF.mem_support_pure_iff] at h; subst out; rfl)

end CryptoOracle.Interactive.RawTapeEquality
