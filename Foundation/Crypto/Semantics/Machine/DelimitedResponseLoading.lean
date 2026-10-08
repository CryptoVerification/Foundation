import Foundation.Crypto.Semantics.Machine.NativeDelimitedTransfer
import Foundation.Crypto.Semantics.ProcedureCompletion

/-! Operational cell-by-cell loading of an external response in delimiter
encoding. The response buffer contains only the received raw bits. Four
explicit write/move transitions handle each bit and two handle the delimiter.
This is a response-port controller, not a claim of a standalone native source
program. Existing public prefix cells are physically present at entry. -/
namespace Machine.DelimitedResponseLoading
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

inductive Control where
  | flag : Configuration → List Bool → Control
  | moveFlag : Configuration → Bool → List Bool → Control
  | payload : Configuration → Bool → List Bool → Control
  | movePayload : Configuration → List Bool → Control
  | terminate : Configuration → Control
  | done : Configuration → Control

def write (machine : Configuration) (bit : Bool) : Configuration :=
  (machine.updateTape .input (fun tape => tape.write (some bit))).advance

def move (machine : Configuration) : Configuration :=
  (machine.updateTape .input Tape.moveRight).advance

theorem write_instruction (machine : Configuration) (bit : Bool) :
    Instruction.next (.write .input bit) machine = .inl (write machine bit) := rfl

theorem move_instruction (machine : Configuration) :
    Instruction.next (.moveRight .input) machine = .inl (move machine) := rfl

noncomputable def step : Control → PMF Control
  | .flag machine [] => PMF.pure (.terminate (write machine false))
  | .flag machine (bit :: rest) => PMF.pure (.moveFlag (write machine true) bit rest)
  | .moveFlag machine bit rest => PMF.pure (.payload (move machine) bit rest)
  | .payload machine bit rest => PMF.pure (.movePayload (write machine bit) rest)
  | .movePayload machine rest => PMF.pure (.flag (move machine) rest)
  | .terminate machine => PMF.pure (.done (move machine))
  | .done machine => PMF.pure (.done machine)

def start (prefixBits : List Bool) (other : Tape) (pc : Nat) : Configuration :=
  {pc := pc, inputTape := NativeDelimitedTransfer.destination prefixBits, outputTape := other}

def finish (prefixBits response : List Bool) (other : Tape) (pc : Nat) : Configuration :=
  {pc := pc + 4 * response.length + 2,
   inputTape := NativeDelimitedTransfer.destination (prefixBits ++ FiniteBitEncoding.delimit response), outputTape := other}

theorem iteration (prefixBits : List Bool) (bit : Bool) (rest : List Bool) (other : Tape) (pc : Nat) :
    eval step 4 (.flag (start prefixBits other pc) (bit :: rest)) =
      PMF.pure (.flag (start (prefixBits ++ [true, bit]) other (pc + 4)) rest) := by
  cases bit <;> simp [eval, step, start, write, move, NativeDelimitedTransfer.destination,
    Configuration.updateTape, Configuration.advance, Tape.write, Tape.moveRight, List.reverse_append, Nat.add_assoc]

theorem run (prefixBits response : List Bool) (other : Tape) (pc : Nat) :
    eval step (4 * response.length + 2) (.flag (start prefixBits other pc) response) =
      PMF.pure (.done (finish prefixBits response other pc)) := by
  induction response generalizing prefixBits pc with
  | nil =>
      simp [eval, step, start, finish, write, move, NativeDelimitedTransfer.destination,
        FiniteBitEncoding.delimit, Configuration.updateTape, Configuration.advance,
        Tape.write, Tape.moveRight, List.reverse_append, Nat.add_assoc]
  | cons bit rest ih =>
      rw [show 4 * (bit :: rest).length + 2 = 4 + (4 * rest.length + 2) by simp; omega,
        eval_add, iteration, PMF.pure_bind, ih]
      congr 1
      simp [finish, FiniteBitEncoding.delimit, List.append_assoc]
      omega

def terminal : Control → Prop
  | .done _ => True
  | _ => False

theorem absorbing (state : Control) (h : terminal state) : step state = PMF.pure state := by
  cases state <;> simp_all [terminal, step]

/-- The loader has a real finite operational contract. The response encoding
appears in the postcondition, not as a precomputed input to the controller. -/
noncomputable def procedure (prefixBits response : List Bool) (other : Tape) (pc : Nat) :
    TimedExecution.Procedure step Unit Configuration :=
  TimedExecution.Procedure.ofFixed step (fun _ => .flag (start prefixBits other pc) response) (fun _ machine => .done machine)
    (fun _ => PMF.pure (finish prefixBits response other pc)) (fun _ => 4 * response.length + 2)
    (fun _ => by simpa only [PMF.pure_map] using run prefixBits response other pc)

noncomputable def completion (prefixBits response : List Bool) (other : Tape) (pc : Nat) :
    Completion step (.flag (start prefixBits other pc) response) terminal :=
  Completion.ofProcedure (procedure prefixBits response other pc) rfl (fun _ _ => trivial)

/-- Every prefix of a longer analysis horizon keeps the completed loader
state; no additional response writes occur after completion. -/
theorem run_horizon (prefixBits response : List Bool) (other : Tape) (pc horizon : Nat)
    (hTime : 4 * response.length + 2 ≤ horizon) :
    eval step horizon (.flag (start prefixBits other pc) response) =
      PMF.pure (.done (finish prefixBits response other pc)) := by
  have h := (completion prefixBits response other pc).final_run absorbing horizon hTime
  change eval step horizon (.flag (start prefixBits other pc) response) =
    (PMF.pure (finish prefixBits response other pc)).map Control.done at h
  simpa only [PMF.pure_map] using h

end Machine.DelimitedResponseLoading
