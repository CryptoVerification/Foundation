import Foundation.Crypto.Semantics.Machine.NativeDelimitedTransfer

/-! A fixed native scan from the start of a raw bitstring to its first blank.
Saved left-hand bits and the complete other tape are retained. -/
namespace Machine.NativeBitstringSeekEnd
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

structure Input where
  before : List Bool := []
  data : List Bool
  other : Tape := {}

def code : Program := [.branch .input 3 1 1, .moveRight .input, .jump 0, .halt]

def initial (input : Input) : Configuration :=
  {inputTape := {Tape.ofBits input.data with left := input.before.reverse.map some}, outputTape := input.other}

def finish (input : Input) : Configuration :=
  {pc := 3, inputTape := NativeDelimitedTransfer.destination (input.before ++ input.data),
   outputTape := input.other, halted := true}

theorem iteration (input : Input) (bit : Bool) (rest : List Bool) :
    evalConfigWithin code (initial {input with data := bit :: rest}) 3 =
      PMF.pure (initial {input with before := input.before ++ [bit], data := rest}) := by
  cases bit <;> cases rest <;>
    simp [code, initial, evalConfigWithin, stepPMF, next, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.ofBits, Tape.moveRight, List.reverse_append]

theorem run (input : Input) :
    evalConfigWithin code (initial input) (3 * input.data.length + 2) = PMF.pure (finish input) := by
  obtain ⟨before, data, other⟩ := input
  induction data generalizing before with
  | nil => simp [code, initial, finish, NativeDelimitedTransfer.destination, Tape.ofBits,
      evalConfigWithin, stepPMF, next, Instruction.next, Configuration.tape]
  | cons bit rest ih =>
      rw [show 3 * ({before := before, data := bit :: rest, other := other} : Input).data.length + 2 =
        3 + (3 * rest.length + 2) by simp; omega,
        evalConfigWithin_add, iteration ⟨before, rest, other⟩ bit rest, PMF.pure_bind, ih]
      simp [finish, List.append_assoc]

noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed code initial (fun _ output => output) (fun input => PMF.pure (finish input))
    (fun input => 3 * input.data.length + 2) (fun input => by simpa only [PMF.pure_map] using run input)
    (by decide) (fun _ => by change 0 < 4; decide) (fun _ => rfl)
    (by intro input output h; rw [PMF.mem_support_pure_iff] at h; subst output; rfl)

end Machine.NativeBitstringSeekEnd
