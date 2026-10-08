import Foundation.Crypto.Semantics.Machine.NativePacketPreparation
import Foundation.Crypto.Semantics.Machine.BackwardErasureExactClock

/-! A charged packet handoff: write, rewind, then erase the source block.
Arbitrary saved regions remain explicit. With empty saved regions the
endpoint is cell-equivalent to a standard packet input on the opposite
tape. The finite blank layout is still preserved, not normalized for free. -/
namespace Machine.NativePacketHandoff
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

structure Input where
  data : List Bool
  before : List (Option Bool) := []
  sourceSuffix : List (Option Bool) := []
  packetSuffix : List (Option Bool) := []

def packetInput (input : Input) : NativePacketPreparation.Input :=
  { data := input.data
    inputFrame := none :: input.before
    inputSuffix := input.sourceSuffix
    outputSuffix := input.packetSuffix }

def eraseInput (input : Input) : NativeBackwardErasure.Input :=
  { bits := input.data
    before := input.before
    right := input.sourceSuffix
    other := (NativePacketPreparation.finish (packetInput input)).outputTape }

noncomputable def packet : NativeComponent Input Configuration :=
  NativePacketPreparation.link.component.reindex packetInput

noncomputable def link : TypedNativeComposition.Link packet.procedure NativeBackwardErasure.inputComponent.procedure :=
  packet.link NativeBackwardErasure.inputComponent
    (fun _ machine => {machine.resumeAt 21 with halted := true})
    (by
      intro input output h
      change output ∈ (NativePacketPreparation.link.native.execution.semantics (packetInput input)).support at h
      rw [NativePacketPreparation.semantics, PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun input _ => eraseInput input)
    (by
      intro input output h
      change output ∈ (NativePacketPreparation.link.native.execution.semantics (packetInput input)).support at h
      rw [NativePacketPreparation.semantics, PMF.mem_support_pure_iff] at h
      subst output
      change (NativeBackwardErasure.initial (eraseInput input)).swapTapes.rebasePc 23 =
        (NativePacketPreparation.finish (packetInput input)).resumeAt 23
      rfl)
    (fun input => 4 * input.data.length + 3)
    (fun _ _ _ => Nat.le_refl _)

def initial (input : Input) : Configuration := NativePacketPreparation.initial (packetInput input)

def finish (input : Input) : Configuration :=
  {(NativeBackwardErasure.finish (eraseInput input)).swapTapes.resumeAt 29 with halted := true}

theorem code : link.code =
    (NativeFlaggedRequest.code.followedBy rewindBitstring.swapTapes).followedBy eraseOutputBlock.swapTapes := rfl

def fixedCode : Program := NativePacketPreparation.fixedCode.followedBy eraseOutputBlock.swapTapes

theorem fixedCode_eq : fixedCode = link.code := rfl

theorem code_length : link.code.length = 30 := by
  rw [link.code_length]
  change NativePacketPreparation.link.code.length + 5 + 3 = 30
  rw [NativePacketPreparation.code_length]

theorem budget (input : Input) : link.native.execution.budget input = 16 * input.data.length + 15 := by
  rw [link.budget]
  change NativePacketPreparation.link.native.execution.budget (packetInput input) + (4 * input.data.length + 3) + 1 = _
  rw [NativePacketPreparation.budget]
  simp only [packetInput]
  omega

theorem semantics (input : Input) : link.native.execution.semantics input = PMF.pure (finish input) := by
  rw [link.semantics]
  change (NativePacketPreparation.link.native.execution.semantics (packetInput input)).bind _ = _
  rw [NativePacketPreparation.semantics, PMF.pure_bind]
  change (PMF.pure (NativeBackwardErasure.finish (eraseInput input))).map _ = _
  rw [PMF.pure_map]
  rfl

theorem run (input : Input) (horizon : Nat) (hTime : 16 * input.data.length + 15 ≤ horizon) :
    evalConfigWithin link.code (initial input) horizon = PMF.pure (finish input) := by
  have h := link.run input horizon (by
    change link.native.execution.budget input ≤ horizon
    rw [budget]
    exact hTime)
  exact h.trans (semantics input)

theorem firstArrival_joint (input : Input) :
    link.component.firstArrival.procedure.execution.costed input =
      PMF.pure (finish input, 16 * input.data.length + 15) := by
  rw [link.firstArrival_costed_from_components]
  change (NativePacketPreparation.link.component.firstArrival.procedure.execution.costed (packetInput input)).bind
    (fun first => (NativeBackwardErasure.inputComponent.firstArrival.procedure.execution.costed
      (eraseInput input)).map (fun second =>
        ({second.1.resumeAt link.finalPc with halted := true}, first.2 + second.2 + 1))) = _
  rw [NativePacketPreparation.firstArrival_joint, PMF.pure_bind,
    NativeBackwardErasure.input_firstArrival_joint, PMF.pure_map]
  congr 1
  apply Prod.ext
  · rfl
  · change 12 * input.data.length + 11 + (4 * input.data.length + 3) + 1 = _
    omega

theorem finish_input (input : Input) : (finish input).inputTape =
    {left := input.before, right := List.replicate (input.data.length + 1) none ++ input.sourceSuffix} := by
  exact NativeBackwardErasure.output_cells (eraseInput input)

theorem finish_output (input : Input) : (finish input).outputTape =
    ({right := (FiniteBitEncoding.delimit input.data).map some ++ none :: input.packetSuffix} : Tape).moveRight := rfl

/-- After actual erasure, the work tape contains no old source bits. -/
theorem clean_input (input : Input) (hBefore : input.before = []) (hSuffix : input.sourceSuffix = []) :
    (finish input).inputTape.Equivalent ({} : Tape) :=
  NativeBackwardErasure.output_blank (eraseInput input) hBefore hSuffix

/-- The prepared packet has the same cells and head position as a standard
input. Relabeling the observer's tape operands will consume these cells;
this theorem itself does not execute a tape swap. -/
theorem clean_entry (input : Input) (hBefore : input.before = [])
    (hSource : input.sourceSuffix = []) (hPacket : input.packetSuffix = []) :
    ((finish input).resumeAt 0).Equivalent
      (Configuration.initial (FiniteBitEncoding.delimit input.data)).swapTapes := by
  refine ⟨rfl, rfl, clean_input input hBefore hSource, ?_⟩
  change (finish input).outputTape.Equivalent (Tape.ofBits (FiniteBitEncoding.delimit input.data))
  rw [finish_output, hPacket]
  exact rewindBitstringFinish_input_equivalent (FiniteBitEncoding.delimit input.data) ({} : Tape)

def inputSize (input : Input) : Nat := input.data.length + input.before.length +
  input.sourceSuffix.length + input.packetSuffix.length

theorem budget_bound (input : Input) : link.native.execution.budget input ≤ 16 * inputSize input + 15 := by
  rw [budget]
  unfold inputSize
  omega

theorem initial_cells (input : Input) : (initial input).tapeCells =
    3 * input.data.length + 4 + input.before.length + input.sourceSuffix.length + input.packetSuffix.length := by
  have h := NativePacketPreparation.initial_cells (packetInput input)
  change (initial input).tapeCells = _ at h
  simp only [packetInput, List.length_cons] at h
  omega

theorem initial_cells_bound (input : Input) : (initial input).tapeCells ≤ 3 * inputSize input + 4 := by
  rw [initial_cells]
  unfold inputSize
  omega

def bitBound (size : Nat) : Nat :=
  StructuredCodeEncoding.bound fixedCode 0 (3 * size + 4) (16 * size + 15)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 4))
    (((PolynomiallyBounded.const 16).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 15))

theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ 16 * input.data.length + 15)
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF link.code) elapsed (initial input)).support) :
    (StructuredCodeEncoding.completeEncoding.encode (link.code, state)).length ≤ bitBound (inputSize input) :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (initial_cells_bound input) (by unfold inputSize; omega))

end Machine.NativePacketHandoff
