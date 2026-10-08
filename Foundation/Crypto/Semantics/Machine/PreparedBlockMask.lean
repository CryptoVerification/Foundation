import Foundation.Crypto.Semantics.Machine.RetainedCopyCleanup
import Foundation.Crypto.Semantics.Machine.NativeEquivalentEntry
import Foundation.Crypto.Semantics.Machine.FlaggedBlockXorComponent
import Foundation.Crypto.Semantics.Machine.PairPreparation

/-! One finite program copies a stored key after a physically present
request, rewinds the request, erases the source key, and masks the message.
The masking code is compiled for the opposite tape roles and runs on the
actual blank-padded representation. This is an internal component, not a
public experiment: the request/key scratch tape is still retained at exit. -/
namespace Machine.PreparedBlockMask
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

abbrev Input := FlaggedBlockXor.Component.Input

def preparationInput (input : Input) : RetainedCopyCleanup.Input :=
  (input.key, FlaggedBlockXor.request input.message)

noncomputable def preparation : NativeComponent Input Configuration :=
  RetainedCopyCleanup.link.component.reindex preparationInput

theorem preparation_entry (input : Input) : preparation.procedure.execution.entry input =
    RetainedCopy.copying [] input.key ((FlaggedBlockXor.request input.message).reverse.map some) := by
  change RetainedCopyCleanup.link.native.execution.entry (preparationInput input) = _
  rw [RetainedCopyCleanup.link.native_entry, RetainedCopyRewind.link.native_entry]
  rfl

theorem preparation_budget (input : Input) :
    preparation.procedure.execution.budget input = 18 * input.message.length + 15 := by
  change RetainedCopyCleanup.link.native.execution.budget (preparationInput input) = _
  rw [RetainedCopyCleanup.budget]
  simp only [preparationInput, FlaggedBlockXor.request_length, input.sameLength]
  omega

noncomputable def mask : NativeComponent
    (NativeComponent.EquivalentInput FlaggedBlockXor.Component.component.swapTapes) Configuration :=
  FlaggedBlockXor.Component.component.swapTapes.equivalentEntries

def maskInput (input : Input) : NativeComponent.EquivalentInput FlaggedBlockXor.Component.component.swapTapes where
  logical := input
  actual := (RetainedCopyCleanup.finish (preparationInput input)).resumeAt 0
  equivalent := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact RetainedCopyCleanup.source_blank (preparationInput input)
    · change (RetainedCopyCleanup.finish (preparationInput input)).outputTape.Equivalent
        (ResponseExport.fromCells ((FlaggedBlockXor.request input.message ++ input.key).map some ++ [none]))
      exact (RetainedCopyCleanup.output_equivalent (preparationInput input)).trans
        (PairPreparation.prepared_equivalent (FlaggedBlockXor.request input.message ++ input.key)).symm

noncomputable def link : TypedNativeComposition.Link preparation.procedure mask.procedure :=
  preparation.link mask (fun _ machine => {machine.resumeAt 26 with halted := true})
    (by
      intro input output h
      change output ∈ (RetainedCopyCleanup.link.native.execution.semantics (preparationInput input)).support at h
      rw [RetainedCopyCleanup.semantics, PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun input _ => maskInput input)
    (by
      intro input output h
      change output ∈ (RetainedCopyCleanup.link.native.execution.semantics (preparationInput input)).support at h
      rw [RetainedCopyCleanup.semantics, PMF.mem_support_pure_iff] at h
      subst output
      change ((RetainedCopyCleanup.finish (preparationInput input)).resumeAt 0).rebasePc _ = _
      simp only [Configuration.resumeAt, Configuration.rebasePc, Configuration.mk.injEq,
        Nat.add_zero, and_true, true_and]
      exact ⟨rfl, rfl⟩)
    (fun input => 24 * input.message.length + 8) (fun _ _ _ => Nat.le_refl _)

theorem code : link.code = RetainedCopyCleanup.link.code.followedBy FlaggedBlockXor.code.swapTapes := rfl

theorem code_length : link.code.length = 67 := by
  rw [link.code_length]
  change RetainedCopyCleanup.link.code.length + FlaggedBlockXor.code.swapTapes.length + 3 = 67
  rw [RetainedCopyCleanup.code_length, Program.swapTapes_length]
  rfl

theorem budget (input : Input) : link.native.execution.budget input = 42 * input.message.length + 24 := by
  rw [link.budget]
  change RetainedCopyCleanup.link.native.execution.budget (preparationInput input) +
    (24 * input.message.length + 8) + 1 = _
  rw [RetainedCopyCleanup.budget]
  simp only [preparationInput, FlaggedBlockXor.request_length, input.sameLength]
  omega

theorem mask_observation (input : Input) :
    (mask.procedure.execution.semantics (maskInput input)).map (fun machine => machine.inputTape.bits) =
      PMF.pure (OneTimePad.xorList input.key input.message) := by
  have h := FlaggedBlockXor.Component.component.swapTapes.equivalentEntries_observe (maskInput input)
    (fun machine => machine.inputTape.bits) (fun _ _ h => h.2.2.1.bits)
  change (mask.procedure.execution.semantics (maskInput input)).map (fun machine => machine.inputTape.bits) =
    (PMF.pure (FlaggedBlockXor.final input.key input.message)).map (fun machine => machine.outputBits) at h
  simpa only [PMF.pure_map, FlaggedBlockXor.final_output] using h

theorem semantics (input : Input) : link.native.execution.semantics input =
    (mask.procedure.execution.semantics (maskInput input)).map
      (fun machine => {machine.resumeAt 66 with halted := true}) := by
  rw [link.semantics]
  change (RetainedCopyCleanup.link.native.execution.semantics (preparationInput input)).bind _ = _
  rw [RetainedCopyCleanup.semantics, PMF.pure_bind]
  rfl

theorem ciphertext (input : Input) :
    (link.native.execution.semantics input).map (fun machine => machine.inputTape.bits) =
      PMF.pure (OneTimePad.xorList input.key input.message) := by
  rw [semantics, PMF.map_comp]
  exact mask_observation input

theorem run (input : Input) (horizon : Nat) (hTime : 42 * input.message.length + 24 ≤ horizon) :
    (evalConfigWithin link.code (RetainedCopy.copying [] input.key
      ((FlaggedBlockXor.request input.message).reverse.map some)) horizon).map
        (fun machine => machine.inputTape.bits) = PMF.pure (OneTimePad.xorList input.key input.message) := by
  have h := link.run input horizon (by change link.native.execution.budget input ≤ horizon; rw [budget]; exact hTime)
  exact (congrArg (fun distribution => distribution.map (fun machine => machine.inputTape.bits)) h).trans
    (ciphertext input)

theorem operational : TimedExecution.Procedure.Operational link.native.execution := link.operational

noncomputable def spaceProfile : Nat → Nat :=
  link.storageProfile (fun _ => 0) (fun size => 3 * size + 3)
    (fun size => 18 * size + 15) (fun size => 24 * size + 8)

theorem space_polynomial : PolynomiallyBounded spaceProfile :=
  link.storageProfile_polynomial (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 3))
    (((PolynomiallyBounded.const 18).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 15))
    (((PolynomiallyBounded.const 24).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 8))

theorem storage_peak (input : Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ 42 * input.message.length + 24) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF link.code) elapsed
      (RetainedCopy.copying [] input.key ((FlaggedBlockXor.request input.message).reverse.map some))).support) :
    (NativeEncodedResources.completeEncoding.encode (link.code, target)).length ≤
      spaceProfile input.message.length := by
  apply link.storage_profile (fun _ => 0) (fun size => 3 * size + 3)
    (fun size => 18 * size + 15) (fun size => 24 * size + 8)
    (fun size value => value.message.length = size)
    _ _ _ _ input.message.length input rfl elapsed
    (by change elapsed ≤ link.native.execution.budget input; rw [budget]; exact hElapsed) target
    (by rw [preparation_entry]; exact hTarget)
  · intro size value _
    rw [preparation_entry]
    exact Nat.le_refl 0
  · intro size value hSize
    rw [preparation_entry]
    have hi := Tape.cells_ofBits_le value.key
    change ({Tape.ofBits value.key with left := []} : Tape).cells +
      ({left := (FlaggedBlockXor.request value.message).reverse.map some} : Tape).cells ≤ _
    simp only [Tape.cells, List.length_nil, List.length_map, List.length_reverse, Nat.zero_add,
      FlaggedBlockXor.request_length]
    simp only [Tape.cells] at hi
    have hKey := value.sameLength
    omega
  · intro size value hSize
    rw [preparation_budget, hSize]
  · intro size value hSize
    change 24 * value.message.length + 8 ≤ _
    omega

end Machine.PreparedBlockMask
