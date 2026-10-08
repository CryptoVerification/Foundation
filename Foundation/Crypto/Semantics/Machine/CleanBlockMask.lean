import Foundation.Crypto.Semantics.Machine.PreparedBlockMaskLayout
import Foundation.Crypto.Semantics.Machine.NativeEquivalentComposition
import Foundation.Crypto.Semantics.Machine.NativeBackwardErasure

/-! Mask a physically present request and then erase its retained scratch
block. The ciphertext tape is retained. The full exit remains the actual
finite representation; this does not yet construct the public experiment. -/
namespace Machine.CleanBlockMask
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

abbrev Input := PreparedBlockMask.Input

def eraseInput (input : Input) : NativeBackwardErasure.Input :=
  { bits := FlaggedBlockXor.request input.message ++ input.key,
    other := (FlaggedBlockXor.final input.key input.message).outputTape }

theorem handoff (input : Input) (output : Configuration)
    (hOutput : output ∈ (PreparedBlockMask.link.native.execution.semantics input).support) :
    (output.resumeAt 0).Equivalent (NativeBackwardErasure.component.procedure.execution.entry (eraseInput input)) := by
  have h := (PreparedBlockMask.exit_equivalent input output hOutput).resumeAt 0
  change (output.resumeAt 0).Equivalent
    ({inputTape := (FlaggedBlockXor.final input.key input.message).outputTape,
      outputTape := (FlaggedBlockXor.final input.key input.message).inputTape} : Configuration) at h
  rw [FlaggedBlockXor.Layout.final_inputTape] at h
  exact h

noncomputable def link : TypedNativeComposition.Link PreparedBlockMask.link.native
    NativeBackwardErasure.component.equivalentEntries.procedure :=
  PreparedBlockMask.link.appendEquivalent NativeBackwardErasure.component (fun input _ => eraseInput input)
    handoff (fun input => 12 * input.message.length + 7) (by
      intro input _ _
      change 4 * (FlaggedBlockXor.request input.message ++ input.key).length + 3 ≤ _
      simp only [List.length_append, FlaggedBlockXor.request_length, input.sameLength]
      omega)

theorem code : link.code = PreparedBlockMask.link.code.followedBy eraseOutputBlock := rfl

theorem code_length : link.code.length = 75 := by
  rw [link.code_length]
  change PreparedBlockMask.link.code.length + 5 + 3 = 75
  rw [PreparedBlockMask.code_length]

theorem budget (input : Input) : link.native.execution.budget input = 54 * input.message.length + 32 := by
  rw [link.budget, PreparedBlockMask.budget]
  change 42 * input.message.length + 24 + (12 * input.message.length + 7) + 1 = _
  omega

def canonicalExit (input : Input) : Configuration :=
  { (NativeBackwardErasure.finish (eraseInput input)).resumeAt 74 with halted := true }

theorem erase_result (input : Input) (middle : Configuration)
    (target : Configuration)
    (hTarget : target ∈ (NativeBackwardErasure.component.equivalentEntries.procedure.execution.semantics
      (PreparedBlockMask.link.equivalentInput NativeBackwardErasure.component (fun input _ => eraseInput input)
        handoff input middle)).support) :
    target.Equivalent (NativeBackwardErasure.finish (eraseInput input)) := by
  apply NativeBackwardErasure.component.equivalentEntries_exit _ (NativeBackwardErasure.finish (eraseInput input)) _ target hTarget
  rw [PreparedBlockMask.link.equivalentInput_logical]
  rfl

theorem exit_equivalent (input : Input) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics input).support) :
    target.Equivalent (canonicalExit input) := by
  rw [link.semantics, PMF.mem_support_bind_iff] at hTarget
  obtain ⟨middle, _, hTarget⟩ := hTarget
  rw [PMF.mem_support_map_iff] at hTarget
  obtain ⟨last, hLast, rfl⟩ := hTarget
  exact ((erase_result input middle last hLast).resumeAt 74).withHalted true

theorem scratch_blank (input : Input) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics input).support) :
    target.outputTape.Equivalent ({} : Tape) :=
  (exit_equivalent input target hTarget).2.2.2.trans
    (NativeBackwardErasure.output_blank (eraseInput input) rfl rfl)

theorem ciphertext (input : Input) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics input).support) :
    target.inputTape.bits = OneTimePad.xorList input.key input.message := by
  have h := (exit_equivalent input target hTarget).2.2.1.bits
  change target.inputTape.bits = (FlaggedBlockXor.final input.key input.message).outputBits at h
  exact h.trans (FlaggedBlockXor.final_output _ _)

theorem observation (input : Input) :
    (link.native.execution.semantics input).map (fun machine => (machine.inputTape.bits, machine.outputTape.bits)) =
      PMF.pure (OneTimePad.xorList input.key input.message, []) := by
  have h : (link.native.execution.semantics input).map (fun machine => (machine.inputTape.bits, machine.outputTape.bits)) =
      (link.native.execution.semantics input).map (fun _ => (OneTimePad.xorList input.key input.message, [])) := by
    rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext target hTarget
    have hBlank : target.outputTape.bits = [] := (scratch_blank input target hTarget).bits
    change PMF.pure (target.inputTape.bits, target.outputTape.bits) =
      PMF.pure (OneTimePad.xorList input.key input.message, [])
    rw [ciphertext input target hTarget, hBlank]
  exact h.trans (PMF.map_const _ _)

theorem run (input : Input) (horizon : Nat) (hTime : 54 * input.message.length + 32 ≤ horizon) :
    (evalConfigWithin link.code (RetainedCopy.copying [] input.key
      ((FlaggedBlockXor.request input.message).reverse.map some)) horizon).map
        (fun machine => (machine.inputTape.bits, machine.outputTape.bits)) =
      PMF.pure (OneTimePad.xorList input.key input.message, []) := by
  have h := link.run input horizon (by change link.native.execution.budget input ≤ horizon; rw [budget]; exact hTime)
  exact (congrArg (fun distribution => distribution.map (fun machine => (machine.inputTape.bits, machine.outputTape.bits))) h).trans
    (observation input)

theorem operational : TimedExecution.Procedure.Operational link.native.execution := link.operational

noncomputable def spaceProfile : Nat → Nat :=
  link.storageProfile (fun _ => 0) (fun size => 3 * size + 3)
    (fun size => 42 * size + 24) (fun size => 12 * size + 7)

theorem space_polynomial : PolynomiallyBounded spaceProfile :=
  link.storageProfile_polynomial (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 3))
    (((PolynomiallyBounded.const 42).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 24))
    (((PolynomiallyBounded.const 12).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 7))

theorem storage_peak (input : Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ 54 * input.message.length + 32) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF link.code) elapsed
      (RetainedCopy.copying [] input.key ((FlaggedBlockXor.request input.message).reverse.map some))).support) :
    (NativeEncodedResources.completeEncoding.encode (link.code, target)).length ≤
      spaceProfile input.message.length := by
  apply link.storage_profile (fun _ => 0) (fun size => 3 * size + 3)
    (fun size => 42 * size + 24) (fun size => 12 * size + 7)
    (fun size value => value.message.length = size)
    _ _ _ _ input.message.length input rfl elapsed
    (by change elapsed ≤ link.native.execution.budget input; rw [budget]; exact hElapsed) target
    (by rw [PreparedBlockMask.link.native_entry, PreparedBlockMask.preparation_entry]; exact hTarget)
  · intro size value _
    rw [PreparedBlockMask.link.native_entry, PreparedBlockMask.preparation_entry]
    exact Nat.le_refl 0
  · intro size value hSize
    rw [PreparedBlockMask.link.native_entry, PreparedBlockMask.preparation_entry]
    have hi := Tape.cells_ofBits_le value.key
    change ({Tape.ofBits value.key with left := []} : Tape).cells +
      ({left := (FlaggedBlockXor.request value.message).reverse.map some} : Tape).cells ≤ _
    simp only [Tape.cells, List.length_nil, List.length_map, List.length_reverse, Nat.zero_add,
      FlaggedBlockXor.request_length]
    simp only [Tape.cells] at hi
    have hKey := value.sameLength
    omega
  · intro size value hSize
    rw [PreparedBlockMask.budget, hSize]
  · intro size value hSize
    change 12 * value.message.length + 7 ≤ _
    omega

end Machine.CleanBlockMask
