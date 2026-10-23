import Foundation.Crypto.Semantics.Oracle.ResponseLoading
import Foundation.Crypto.Semantics.Oracle.StraightLine

/-! Native admission adapter from a loaded three-bit request to ten bits.
The original server program is retained as the prefix. Twenty-nine actual
instructions pad its output tape and jump to the original server entry.
The private input/cache tape, oracle state and transcript are unchanged.
-/
namespace CryptoOracle.Interactive.NativeCompactRequest
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def pad : Code :=
  [.native (.moveRight .output), .native (.moveRight .output), .native (.moveRight .output),
   .native (.write .output false), .native (.moveRight .output),
   .native (.write .output false), .native (.moveRight .output),
   .native (.write .output false), .native (.moveRight .output),
   .native (.write .output false), .native (.moveRight .output),
   .native (.write .output false), .native (.moveRight .output),
   .native (.write .output false), .native (.moveRight .output),
   .native (.write .output false), .native (.moveRight .output),
   .native (.erase .output),
   .native (.moveLeft .output), .native (.moveLeft .output), .native (.moveLeft .output),
   .native (.moveLeft .output), .native (.moveLeft .output), .native (.moveLeft .output),
   .native (.moveLeft .output), .native (.moveLeft .output), .native (.moveLeft .output),
   .native (.moveLeft .output)]

def adapter (entry : Nat) : Code := pad ++ [.native (.jump entry)]

def actions : List StraightLine.Action :=
  [.right .output, .right .output, .right .output,
   .write .output (some false), .right .output, .write .output (some false), .right .output,
   .write .output (some false), .right .output, .write .output (some false), .right .output,
   .write .output (some false), .right .output, .write .output (some false), .right .output,
   .write .output (some false), .right .output, .write .output none,
   .left .output, .left .output, .left .output, .left .output, .left .output,
   .left .output, .left .output, .left .output, .left .output, .left .output]

theorem pad_actions : pad = StraightLine.code actions := rfl
theorem actions_length : actions.length = 28 := rfl

def code (source : Code) (entry : Nat) : Code := source ++ adapter entry

theorem pad_length : pad.length = 28 := rfl
theorem adapter_length (entry : Nat) : (adapter entry).length = 29 := rfl

theorem fetch (source : Code) (entry position : Nat) :
    (code source entry)[source.length + position]? = (adapter entry)[position]? := by
  simp [code, List.getElem?_append_right]

theorem fetch_start (source : Code) (entry : Nat) :
    (code source entry)[source.length]? = some (.native (.moveRight .output)) := by
  simpa only [Nat.add_zero, adapter, pad, List.cons_append, List.getElem?_cons_zero] using fetch source entry 0

theorem fetch_jump (source : Code) (entry : Nat) :
    (code source entry)[source.length + 28]? = some (.native (.jump entry)) := by
  rw [fetch]
  rfl

def start (source : Code) (machine : Machine.Configuration) (first second third : Bool) : Machine.Configuration :=
  { machine with pc := source.length, halted := false, outputTape := ResponseLoading.loaded [first, second, third] }

def finish (entry : Nat) (machine : Machine.Configuration) (first second third : Bool) : Machine.Configuration :=
  { machine with
    pc := entry
    halted := false
    outputTape := ResponseLoading.loaded ([first, second, third] ++ List.replicate 7 false) }

theorem checked (source : Code) (machine : Machine.Configuration) (first second third : Bool) :
    StraightLine.execute actions (start source machine first second third) =
      finish (source.length + 28) machine first second third := by
  rfl

theorem prefix_run {State : Type} (source : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (machine : Machine.Configuration)
    (first second third : Bool) :
    TimedExecution.eval (Reification.timedStep (source ++ pad) oracle) 28
      (⟨state, .running (start source machine first second third), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (finish (source.length + 28) machine first second third), trace⟩ := by
  have placed := StraightLine.public_run oracle state trace source [] actions
    (start source machine first second third) rfl rfl
  simpa only [actions_length, ← pad_actions, List.append_nil, checked] using placed

theorem run {State : Type} (source : Code) (entry : Nat) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (machine : Machine.Configuration)
    (first second third : Bool) :
    TimedExecution.eval (Reification.timedStep (code source entry) oracle) 29
      (⟨state, .running (start source machine first second third), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (finish entry machine first second third), trace⟩ := by
  have extended := StraightLine.public_run oracle state trace source [.native (.jump entry)] actions
    (start source machine first second third) rfl rfl
  have before : TimedExecution.eval (Reification.timedStep (code source entry) oracle) 28
      (⟨state, .running (start source machine first second third), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (finish (source.length + 28) machine first second third), trace⟩ := by
    simpa only [code, adapter, actions_length, ← pad_actions, checked, List.append_assoc] using extended
  rw [show 29 = 28 + 1 by rfl, TimedExecution.eval_add, before, PMF.pure_bind]
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, Reification.perform,
    Reification.action, transition, finish, fetch_jump, Machine.Instruction.next]

/-- Load the actual compact request, execute all padding instructions and
enter the original backend on the same retained physical machine. -/
theorem load_run {State : Type} (source : Code) (entry : Nat) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (machine : Machine.Configuration)
    (first second third : Bool) :
    TimedExecution.eval (Reification.timedStep (code source entry) oracle) 40
      (⟨state, .loading {machine with pc := source.length, halted := false} [first, second, third] {}, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (finish entry machine first second third), trace⟩ := by
  rw [show 40 = 11 + 29 by decide, TimedExecution.eval_add]
  rw [show 11 = 3 * [first, second, third].length + 2 by rfl, ResponseLoading.run, PMF.pure_bind]
  exact run source entry oracle state trace machine first second third

theorem private_tape (entry : Nat) (machine : Machine.Configuration) (first second third : Bool) :
    (finish entry machine first second third).inputTape = machine.inputTape := rfl

end CryptoOracle.Interactive.NativeCompactRequest
