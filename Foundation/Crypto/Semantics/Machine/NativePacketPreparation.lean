import Foundation.Crypto.Semantics.Machine.NativeDelimitedWriterResources
import Foundation.Crypto.Semantics.Machine.RewindExactClock
import Foundation.Crypto.Semantics.Machine.NativeLinkFirstArrival
import Foundation.Crypto.Semantics.Machine.NativeComponentReindex

/-! Serialize an arbitrary delimited bitstring and position the output head
at the packet's first bit. Both stages execute on the inherited tapes.
Saved source cells and suffixes are retained, including redundant blanks.
The writer capacity is an explicit input precondition, not free allocation.
This is preparation of a packet, not yet a clean observer input. -/
namespace Machine.NativePacketPreparation
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

structure Input where
  data : List Bool
  inputFrame : List (Option Bool) := []
  inputSuffix : List (Option Bool) := []
  outputSuffix : List (Option Bool) := []

def writerInput (input : Input) : NativeDelimitedWriter.Input :=
  { data := input.data
    inputFrame := input.inputFrame
    inputSuffix := input.inputSuffix
    outputSuffix := input.outputSuffix }

def rewindInput (input : Input) : NativeBitstringRewind.Input :=
  { bits := FiniteBitEncoding.delimit input.data
    right := input.outputSuffix
    other := (NativeDelimitedWriter.finish (writerInput input)).inputTape }

noncomputable def writer : NativeComponent Input Configuration :=
  NativeDelimitedWriter.component.reindex writerInput

noncomputable def link : TypedNativeComposition.Link writer.procedure
    NativeBitstringRewind.outputComponent.procedure :=
  writer.link NativeBitstringRewind.outputComponent
    (fun _ machine => {machine.resumeAt 14 with halted := true})
    (by
      intro input output h
      change output ∈ (PMF.pure (NativeDelimitedWriter.finish (writerInput input))).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun input _ => rewindInput input)
    (by
      intro input output h
      change output ∈ (PMF.pure (NativeDelimitedWriter.finish (writerInput input))).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      change (NativeBitstringRewind.initial (rewindInput input)).swapTapes.rebasePc 16 =
        (NativeDelimitedWriter.finish (writerInput input)).resumeAt 16
      change
        ({ pc := 16
           inputTape := (NativeDelimitedWriter.finish (writerInput input)).inputTape
           outputTape :=
             { left := (FiniteBitEncoding.delimit input.data).reverse.map some
               right := input.outputSuffix } } : Configuration) =
        { pc := 16
          inputTape := (NativeDelimitedWriter.finish (writerInput input)).inputTape
          outputTape := (NativeDelimitedWriter.finish (writerInput input)).outputTape }
      rw [NativeDelimitedWriter.finish_output]
      simp [writerInput])
    (fun input => 2 * (FiniteBitEncoding.delimit input.data).length + 4)
    (fun _ _ _ => Nat.le_refl _)

def initial (input : Input) : Configuration := NativeDelimitedWriter.initial (writerInput input)

def finish (input : Input) : Configuration :=
  {(NativeBitstringRewind.finish (rewindInput input)).swapTapes.resumeAt 21 with halted := true}

theorem code : link.code = NativeFlaggedRequest.code.followedBy rewindBitstring.swapTapes := rfl

/-- Executable code construction, independent of the proof-bearing link. -/
def fixedCode : Program := NativeFlaggedRequest.code.followedBy rewindBitstring.swapTapes

theorem fixedCode_eq : fixedCode = link.code := rfl

theorem code_length : link.code.length = 22 := by
  rw [link.code_length]
  rfl

theorem budget (input : Input) : link.native.execution.budget input = 12 * input.data.length + 11 := by
  rw [link.budget]
  change 8 * input.data.length + 4 + (2 * (FiniteBitEncoding.delimit input.data).length + 4) + 1 = _
  rw [FiniteBitEncoding.delimit_length]
  omega

theorem semantics (input : Input) : link.native.execution.semantics input = PMF.pure (finish input) := by
  rw [link.semantics]
  change (PMF.pure (NativeDelimitedWriter.finish (writerInput input))).bind _ = _
  rw [PMF.pure_bind]
  change (PMF.pure (NativeBitstringRewind.finish (rewindInput input))).map _ = _
  rw [PMF.pure_map]
  rfl

theorem run (input : Input) (horizon : Nat) (hTime : 12 * input.data.length + 11 ≤ horizon) :
    evalConfigWithin link.code (initial input) horizon = PMF.pure (finish input) := by
  have h := link.run input horizon (by
    change link.native.execution.budget input ≤ horizon
    rw [budget]
    exact hTime)
  exact h.trans (semantics input)

theorem firstArrival_joint (input : Input) :
    link.component.firstArrival.procedure.execution.costed input =
      PMF.pure (finish input, 12 * input.data.length + 11) := by
  rw [link.firstArrival_costed_from_components]
  change (NativeDelimitedWriter.component.firstArrival.procedure.execution.costed (writerInput input)).bind
    (fun first => (NativeBitstringRewind.outputComponent.firstArrival.procedure.execution.costed
      (rewindInput input)).map (fun second =>
        ({second.1.resumeAt link.finalPc with halted := true}, first.2 + second.2 + 1))) = _
  rw [NativeDelimitedWriter.firstArrival_joint, PMF.pure_bind,
    NativeBitstringRewind.output_firstArrival_joint, PMF.pure_map]
  congr 1
  apply Prod.ext
  · rfl
  · change 8 * input.data.length + 4 + (2 * (FiniteBitEncoding.delimit input.data).length + 4) + 1 = _
    rw [FiniteBitEncoding.delimit_length]
    omega

theorem finish_input (input : Input) : (finish input).inputTape =
    {left := input.data.reverse.map some ++ input.inputFrame, right := input.inputSuffix} := rfl

theorem finish_output (input : Input) : (finish input).outputTape =
    ({right := (FiniteBitEncoding.delimit input.data).map some ++ none :: input.outputSuffix} : Tape).moveRight := rfl

/-- The current output cell is already the first packet bit, even for empty data. -/
theorem finish_head (input : Input) : (finish input).outputTape.current =
    some (if input.data.isEmpty then false else true) := by
  rw [finish_output]
  cases input.data <;> simp [FiniteBitEncoding.delimit, Tape.moveRight]

def inputSize (input : Input) : Nat := input.data.length + input.inputFrame.length +
  input.inputSuffix.length + input.outputSuffix.length

theorem budget_bound (input : Input) : link.native.execution.budget input ≤ 12 * inputSize input + 11 := by
  rw [budget]
  unfold inputSize
  omega

theorem initial_cells (input : Input) : (initial input).tapeCells =
    3 * input.data.length + 3 + input.inputFrame.length + input.inputSuffix.length + input.outputSuffix.length := by
  simpa [initial, writerInput] using NativeDelimitedWriter.initial_cells (writerInput input)

theorem initial_cells_bound (input : Input) : (initial input).tapeCells ≤ 3 * inputSize input + 3 := by
  rw [initial_cells]
  unfold inputSize
  omega

def bitBound (size : Nat) : Nat :=
  StructuredCodeEncoding.bound fixedCode 0 (3 * size + 3) (12 * size + 11)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 3))
    (((PolynomiallyBounded.const 12).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 11))

theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ 12 * input.data.length + 11)
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF link.code) elapsed (initial input)).support) :
    (StructuredCodeEncoding.completeEncoding.encode (link.code, state)).length ≤ bitBound (inputSize input) :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (initial_cells_bound input) (by unfold inputSize; omega))

end Machine.NativePacketPreparation
