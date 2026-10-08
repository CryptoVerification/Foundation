import Foundation.Crypto.Semantics.Machine.RetainedCopyComponent
import Foundation.Crypto.Semantics.Machine.NativeComponentReindex
import Foundation.Crypto.Semantics.Machine.NativeBitstringRewind

/-! Copy a contiguous block after an inherited bit header, then actually
rewind the destination. The source is retained; no runtime tape exchange,
source erasure, or normalization is hidden in the handoff. -/
namespace Machine.RetainedCopyRewind
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

abbrev Input := List Bool × List Bool

noncomputable def copyComponent : NativeComponent Input Configuration :=
  RetainedCopy.Component.component.reindex (fun input => (input.1, input.2.reverse.map some))

def rewindInput (input : Input) : NativeBitstringRewind.Input :=
  { bits := input.2 ++ input.1,
    other := (RetainedCopy.finish input.1 (input.2.reverse.map some)).inputTape }

noncomputable def link :
    TypedNativeComposition.Link copyComponent.procedure NativeBitstringRewind.outputComponent.procedure :=
  copyComponent.link NativeBitstringRewind.outputComponent
    (fun _ machine => {machine.resumeAt 11 with halted := true})
    (by
      intro input output h
      change output ∈ (PMF.pure (RetainedCopy.finish input.1 (input.2.reverse.map some))).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      simp only [RetainedCopy.finish, Configuration.resumeAt, Configuration.mk.injEq,
        and_true, true_and]
      exact ⟨rfl, rfl⟩)
    (fun input _ => rewindInput input)
    (by
      intro input output h
      change output ∈ (PMF.pure (RetainedCopy.finish input.1 (input.2.reverse.map some))).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      change ((NativeBitstringRewind.initial (rewindInput input)).swapTapes).rebasePc _ = _
      simp [NativeBitstringRewind.initial, rewindInput, RetainedCopy.finish,
        Configuration.swapTapes, Configuration.rebasePc, Configuration.resumeAt,
        List.reverse_append, List.map_append]
      exact ⟨rfl, rfl⟩)
    (fun input => 2 * (input.2.length + input.1.length) + 4)
    (by intro input _ _; change 2 * (input.2 ++ input.1).length + 4 ≤ _; simp)

theorem code : link.code = RetainedCopy.code.followedBy rewindBitstring.swapTapes := rfl

theorem code_length : link.code.length = 19 := by
  rw [link.code_length]
  change 12 + rewindBitstring.swapTapes.length + 3 = 19
  rw [Program.swapTapes_length]
  rfl

theorem budget (input : Input) :
    link.native.execution.budget input = 10 * input.1.length + 2 * input.2.length + 10 := by
  rw [link.budget]
  change 8 * input.1.length + 5 + (2 * (input.2.length + input.1.length) + 4) + 1 = _
  omega

def finish (input : Input) : Configuration :=
  { (NativeBitstringRewind.finish (rewindInput input)).swapTapes.resumeAt 18 with halted := true }

theorem semantics (input : Input) : link.native.execution.semantics input = PMF.pure (finish input) := by
  rw [link.semantics]
  change (PMF.pure (RetainedCopy.finish input.1 (input.2.reverse.map some))).bind _ = _
  rw [PMF.pure_bind]
  change (PMF.pure (NativeBitstringRewind.finish (rewindInput input))).map _ = _
  rw [PMF.pure_map]
  rfl

theorem run (input : Input) (horizon : Nat)
    (hTime : 10 * input.1.length + 2 * input.2.length + 10 ≤ horizon) :
    evalConfigWithin link.code (RetainedCopy.copying [] input.1 (input.2.reverse.map some)) horizon =
      PMF.pure (finish input) := by
  have h := link.run input horizon (by
    change link.native.execution.budget input ≤ horizon
    rw [budget]
    exact hTime)
  exact h.trans (semantics input)

theorem operational : TimedExecution.Procedure.Operational link.native.execution := link.operational

theorem retained_source (input : Input) :
    (finish input).inputTape = (RetainedCopy.finish input.1 (input.2.reverse.map some)).inputTape := rfl

/-- The scan exposes the first bit; extra physically represented blanks
remain. This is an observation theorem, not permission to reset the tape. -/
theorem output_equivalent (input : Input) :
    (finish input).outputTape.Equivalent (Tape.ofBits (input.2 ++ input.1)) :=
  rewindBitstringFinish_input_equivalent (input.2 ++ input.1)
    (RetainedCopy.finish input.1 (input.2.reverse.map some)).inputTape

noncomputable def spaceProfile : Nat → Nat :=
  link.storageProfile (fun _ => 0) (fun size => size + 2)
    (fun size => 8 * size + 5) (fun size => 2 * size + 4)

theorem space_polynomial : PolynomiallyBounded spaceProfile :=
  link.storageProfile_polynomial (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 5))
    (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 4))

theorem storage_peak (input : Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ 10 * input.1.length + 2 * input.2.length + 10) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF link.code) elapsed
      (RetainedCopy.copying [] input.1 (input.2.reverse.map some))).support) :
    (NativeEncodedResources.completeEncoding.encode (link.code, target)).length ≤
      spaceProfile (input.1.length + input.2.length) := by
  apply link.storage_profile (fun _ => 0) (fun size => size + 2)
    (fun size => 8 * size + 5) (fun size => 2 * size + 4)
    (fun size value => value.1.length + value.2.length = size)
    _ _ _ _ (input.1.length + input.2.length) input rfl elapsed
    (by change elapsed ≤ link.native.execution.budget input; rw [budget]; exact hElapsed) target hTarget
  · intro size value _
    exact Nat.le_refl 0
  · intro size value hSize
    change (RetainedCopy.copying [] value.1 (value.2.reverse.map some)).tapeCells ≤ _
    have hi := Tape.cells_ofBits_le value.1
    simp only [RetainedCopy.copying, Configuration.tapeCells, Tape.cells,
      List.length_map, List.length_reverse, List.length_nil, Nat.zero_add]
    simp only [Tape.cells] at hi
    omega
  · intro size value hSize
    change 8 * value.1.length + 5 ≤ _
    omega
  · intro size value hSize
    change 2 * (value.2.length + value.1.length) + 4 ≤ _
    omega

end Machine.RetainedCopyRewind
