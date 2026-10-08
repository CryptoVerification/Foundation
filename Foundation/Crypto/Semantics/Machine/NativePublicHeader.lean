import Foundation.Crypto.Semantics.Machine.NativeDelimitedTransfer

/-! Consume and erase a unary public parameter and its terminating false
bit, preserving the following input and the entire other tape. -/
namespace Machine.NativePublicHeader
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

structure Input where
  count : Nat
  suffix : List Bool
  other : Tape := {}
  consumed : Nat := 0

def code : Program :=
  [.branch .input 6 4 1, .erase .input, .moveRight .input, .jump 0,
   .erase .input, .moveRight .input, .halt]

def initial (input : Input) : Configuration :=
  {inputTape := NativeDelimitedTransfer.source input.consumed (List.replicate input.count true ++ false :: input.suffix),
   outputTape := input.other}

def finish (input : Input) : Configuration :=
  {pc := 6, inputTape := NativeDelimitedTransfer.source (input.consumed + input.count + 1) input.suffix,
   outputTape := input.other, halted := true}

theorem iteration (input : Input) :
    evalConfigWithin code (initial {input with count := input.count + 1}) 4 =
      PMF.pure (initial {input with consumed := input.consumed + 1}) := by
  cases h : input.count <;>
    simp [code, initial, h, NativeDelimitedTransfer.source, List.replicate_succ, evalConfigWithin,
      stepPMF, next, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.ofBits, Tape.write, Tape.moveRight, List.replicate_succ]

theorem run (input : Input) :
    evalConfigWithin code (initial input) (4 * input.count + 4) = PMF.pure (finish input) := by
  obtain ⟨count, suffix, other, consumed⟩ := input
  induction count generalizing consumed with
  | zero =>
      cases suffix <;>
        simp [code, initial, finish, NativeDelimitedTransfer.source, evalConfigWithin, stepPMF, next,
          Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
          Tape.ofBits, Tape.write, Tape.moveRight, List.replicate_succ]
  | succ count ih =>
      rw [show 4 * ({count := count + 1, suffix := suffix, other := other, consumed := consumed} : Input).count + 4 =
        4 + (4 * count + 4) by simp; omega,
        evalConfigWithin_add, iteration ⟨count, suffix, other, consumed⟩, PMF.pure_bind, ih]
      congr 1
      simp [finish, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed code initial (fun _ output => output) (fun input => PMF.pure (finish input))
    (fun input => 4 * input.count + 4) (fun input => by simpa only [PMF.pure_map] using run input)
    (by decide) (fun _ => by change 0 < 7; decide) (fun _ => rfl)
    (by intro input output h; rw [PMF.mem_support_pure_iff] at h; subst output; rfl)

end Machine.NativePublicHeader
