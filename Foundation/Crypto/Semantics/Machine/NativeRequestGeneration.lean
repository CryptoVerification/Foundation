import Foundation.Crypto.Semantics.Machine.NativeFixedComponent
import Foundation.Crypto.Semantics.Machine.OneTimePad
import Foundation.Crypto.Semantics.Machine.FlaggedBlockXor

/-! Reusable request writing and contextual random-bit generation.
Both programs are fixed. Their logical concatenations describe actual
cell-by-cell writes at a pre-existing output frontier, not free loaders. -/
namespace Machine
open Foundation.Probability TimedExecution Foundation.Symmetric

structure NativeBitstringContext where
  before : List Bool := []
  prefixBits : List Bool := []
  data : List Bool

namespace NativeFlaggedRequest
set_option backward.isDefEq.respectTransparency false

def code : Program :=
  [.branch .input 12 1 5,
   .write .output true, .moveRight .output, .write .output false, .jump 9,
   .write .output true, .moveRight .output, .write .output true, .jump 9,
   .moveRight .input, .moveRight .output, .jump 0,
   .write .output false, .moveRight .output, .halt]

def initial (input : NativeBitstringContext) : Configuration :=
  OneTimePad.state input.before input.prefixBits input.data

def finish (input : NativeBitstringContext) : Configuration :=
  OneTimePad.finish 14 (input.before ++ input.data)
    (input.prefixBits ++ FlaggedBlockXor.request input.data)

theorem iteration (before prefixBits rest : List Bool) (bit : Bool) :
    evalConfigWithin code (initial ⟨before, prefixBits, bit :: rest⟩) 8 =
      PMF.pure (initial ⟨before ++ [bit], prefixBits ++ [true, bit], rest⟩) := by
  cases bit <;> cases rest <;>
    simp [initial, OneTimePad.state, code, evalConfigWithin, stepPMF, Machine.next,
      Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.ofBits, Tape.write, Tape.moveRight, List.reverse_append]

theorem run (input : NativeBitstringContext) :
    evalConfigWithin code (initial input) (8 * input.data.length + 4) = PMF.pure (finish input) := by
  rcases input with ⟨before, prefixBits, data⟩
  induction data generalizing before prefixBits with
  | nil =>
      simp [initial, finish, OneTimePad.state, OneTimePad.finish, FlaggedBlockXor.request,
        FlaggedBlockXor.messagePrefix, code, evalConfigWithin, stepPMF, Machine.next,
        Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
        Tape.ofBits, Tape.write, Tape.moveRight, List.reverse_append]
  | cons bit rest ih =>
      rw [show 8 * (bit :: rest).length + 4 = 8 + (8 * rest.length + 4) by simp; omega,
        evalConfigWithin_add, iteration, PMF.pure_bind, ih]
      simp [finish, FlaggedBlockXor.request, FlaggedBlockXor.messagePrefix, List.append_assoc]

noncomputable def component : NativeComponent NativeBitstringContext Configuration :=
  NativeComponent.ofFixed code initial (fun _ output => output) (fun input => PMF.pure (finish input))
    (fun input => 8 * input.data.length + 4)
    (fun input => by simpa only [PMF.pure_map] using run input)
    (by decide) (fun _ => by change 0 < 15; decide) (fun _ => rfl)
    (by intro input output h; rw [PMF.mem_support_pure_iff] at h; subst output; rfl)

theorem budget (input : NativeBitstringContext) : component.procedure.execution.budget input =
    8 * input.data.length + 4 := rfl

end NativeFlaggedRequest

namespace NativeContextualSampler

def initial (input : NativeBitstringContext) : Configuration :=
  OneTimePad.state input.before input.prefixBits input.data

def finish (input : NativeBitstringContext) (key : Bits input.data.length) : Configuration :=
  OneTimePad.finish 5 (input.before ++ input.data) (input.prefixBits ++ key.toList)

noncomputable def component : NativeComponent NativeBitstringContext Configuration :=
  NativeComponent.ofFixed OneTimePad.keygen initial (fun _ output => output)
    (fun input => (uniform (Bits input.data.length)).map (finish input))
    (fun input => 5 * input.data.length + 2)
    (fun input => by simpa only [PMF.map_comp, Function.comp_def, initial, finish] using
      OneTimePad.keygen_run input.before input.prefixBits input.data)
    (by decide) (fun _ => by change 0 < 6; decide) (fun _ => rfl)
    (by
      intro input output h
      rw [PMF.mem_support_map_iff] at h
      obtain ⟨key, _, rfl⟩ := h
      rfl)

theorem budget (input : NativeBitstringContext) : component.procedure.execution.budget input =
    5 * input.data.length + 2 := rfl

theorem semantics (input : NativeBitstringContext) : component.procedure.execution.semantics input =
    (uniform (Bits input.data.length)).map (finish input) := rfl

def readKey (input : NativeBitstringContext) (machine : Configuration) : Bits input.data.length :=
  fun index => machine.outputBits[input.prefixBits.length + index.val]?.getD false

theorem readKey_finish (input : NativeBitstringContext) (key : Bits input.data.length) :
    readKey input (finish input key) = key := by
  funext index
  simp [readKey, finish, OneTimePad.finish_output, Bits.toList]

theorem readKey_equivalent (input : NativeBitstringContext) (first second : Configuration)
    (h : first.Equivalent second) : readKey input first = readKey input second := by
  funext index
  simp only [readKey, h.outputBits]

theorem key_distribution (input : NativeBitstringContext) :
    (component.procedure.execution.semantics input).map (readKey input) = uniform (Bits input.data.length) := by
  rw [semantics, PMF.map_comp]
  change (uniform (Bits input.data.length)).map (fun key => readKey input (finish input key)) = _
  simp only [readKey_finish]
  exact PMF.map_id _

end NativeContextualSampler
end Machine
