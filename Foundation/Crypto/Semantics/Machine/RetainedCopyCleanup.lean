import Foundation.Crypto.Semantics.Machine.RetainedCopyRewind
import Foundation.Crypto.Semantics.Machine.NativeForwardErasure

/-! Copy, rewind the destination, and actually erase the retained source.
All three stages are linked finite code. No represented blank is removed
from either tape by the logical input adapter. -/
namespace Machine.RetainedCopyCleanup
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

abbrev Input := RetainedCopyRewind.Input

def eraseInput (input : Input) : NativeForwardErasure.Input :=
  { bits := input.1, before := [none], other := (RetainedCopyRewind.finish input).outputTape }

noncomputable def link :
    TypedNativeComposition.Link RetainedCopyRewind.link.native NativeForwardErasure.component.procedure :=
  RetainedCopyRewind.link.append NativeForwardErasure.component
    (fun input _ => eraseInput input)
    (by
      intro input output h
      rw [RetainedCopyRewind.semantics, PMF.mem_support_pure_iff] at h
      subst output
      change (NativeForwardErasure.initial (eraseInput input)).rebasePc _ = _
      cases input.1 <;>
        simp [NativeForwardErasure.initial, eraseInput, RetainedCopyRewind.finish,
          NativeBitstringRewind.finish, RetainedCopyRewind.rewindInput,
          RetainedCopy.finish, RetainedCopy.restored, Configuration.swapTapes,
          Configuration.rebasePc, Configuration.resumeAt])
    (fun input => 4 * input.1.length + 2)
    (fun _ _ _ => Nat.le_refl _)

theorem code : link.code =
    (RetainedCopy.code.followedBy rewindBitstring.swapTapes).followedBy NativeForwardErasure.code := rfl

theorem code_length : link.code.length = 27 := by
  rw [link.code_length]
  change RetainedCopyRewind.link.code.length + 5 + 3 = 27
  rw [RetainedCopyRewind.code_length]

theorem budget (input : Input) :
    link.native.execution.budget input = 14 * input.1.length + 2 * input.2.length + 13 := by
  rw [link.budget, RetainedCopyRewind.budget]
  change 10 * input.1.length + 2 * input.2.length + 10 + (4 * input.1.length + 2) + 1 = _
  omega

def finish (input : Input) : Configuration :=
  { (NativeForwardErasure.finish (eraseInput input)).resumeAt 26 with halted := true }

theorem semantics (input : Input) : link.native.execution.semantics input = PMF.pure (finish input) := by
  rw [link.semantics, RetainedCopyRewind.semantics, PMF.pure_bind]
  change (PMF.pure (NativeForwardErasure.finish (eraseInput input))).map _ = _
  rw [PMF.pure_map]
  rfl

theorem run (input : Input) (horizon : Nat)
    (hTime : 14 * input.1.length + 2 * input.2.length + 13 ≤ horizon) :
    evalConfigWithin link.code (RetainedCopy.copying [] input.1 (input.2.reverse.map some)) horizon =
      PMF.pure (finish input) := by
  have h := link.run input horizon (by
    change link.native.execution.budget input ≤ horizon
    rw [budget]
    exact hTime)
  rw [RetainedCopyRewind.link.native_entry] at h
  exact h.trans (semantics input)

theorem operational : TimedExecution.Procedure.Operational link.native.execution := link.operational

theorem source_cells (input : Input) : (finish input).inputTape =
    {left := List.replicate input.1.length none ++ [none]} := rfl

theorem source_blank (input : Input) : (finish input).inputTape.Equivalent ({} : Tape) := by
  rw [source_cells]
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro i
  change (List.replicate input.1.length (none : Option Bool) ++ [none]).getD i none = none
  induction input.1.length generalizing i with
  | zero => cases i <;> simp
  | succ n ih =>
      cases i with
      | zero => simp [List.replicate_succ]
      | succ i => simpa only [List.replicate_succ, List.cons_append, List.getD_cons_succ] using ih i

theorem saved_output (input : Input) :
    (finish input).outputTape = (RetainedCopyRewind.finish input).outputTape := rfl

theorem output_equivalent (input : Input) :
    (finish input).outputTape.Equivalent (Tape.ofBits (input.2 ++ input.1)) :=
  RetainedCopyRewind.output_equivalent input

noncomputable def spaceProfile : Nat → Nat :=
  link.storageProfile (fun _ => 0) (fun size => size + 2)
    (fun size => 10 * size + 10) (fun size => 4 * size + 2)

theorem space_polynomial : PolynomiallyBounded spaceProfile :=
  link.storageProfile_polynomial (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 10).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 10))
    (((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 2))

theorem storage_peak (input : Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ 14 * input.1.length + 2 * input.2.length + 13) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF link.code) elapsed
      (RetainedCopy.copying [] input.1 (input.2.reverse.map some))).support) :
    (NativeEncodedResources.completeEncoding.encode (link.code, target)).length ≤
      spaceProfile (input.1.length + input.2.length) := by
  apply link.storage_profile (fun _ => 0) (fun size => size + 2)
    (fun size => 10 * size + 10) (fun size => 4 * size + 2)
    (fun size value => value.1.length + value.2.length = size)
    _ _ _ _ (input.1.length + input.2.length) input rfl elapsed
    (by change elapsed ≤ link.native.execution.budget input; rw [budget]; exact hElapsed) target
    (by rw [RetainedCopyRewind.link.native_entry]; exact hTarget)
  · intro size value _
    rw [RetainedCopyRewind.link.native_entry]
    exact Nat.le_refl 0
  · intro size value hSize
    rw [RetainedCopyRewind.link.native_entry]
    change (RetainedCopy.copying [] value.1 (value.2.reverse.map some)).tapeCells ≤ _
    have hi := Tape.cells_ofBits_le value.1
    simp only [RetainedCopy.copying, Configuration.tapeCells, Tape.cells,
      List.length_map, List.length_reverse, List.length_nil, Nat.zero_add]
    simp only [Tape.cells] at hi
    omega
  · intro size value hSize
    rw [RetainedCopyRewind.budget]
    omega
  · intro size value hSize
    change 4 * value.1.length + 2 ≤ _
    omega

end Machine.RetainedCopyCleanup
