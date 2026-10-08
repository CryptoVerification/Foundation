import Foundation.Crypto.Semantics.Machine.ContextualBlockXorExactTime
import Foundation.Crypto.Semantics.Machine.BackwardErasureExactClock
import Foundation.Crypto.Semantics.Machine.NativeLinkFirstArrival
import Foundation.Crypto.Semantics.Machine.NativeComponentReindex
import Foundation.Crypto.Semantics.Machine.BitstringXorLaws
import Foundation.Crypto.Semantics.Machine.NativeFirstArrivalTimeTransport
import Foundation.Crypto.Semantics.Machine.StructuredCodeEncoding

/-! Native encryption for any supplied equal-length pad and plaintext.
Masking and erasure form one fixed code, with no sampling assumption. The
entry contains the delimited request and pad, plus explicit blank workspace.
Preparing that entry or computing a PRG pad is a separate charged task. -/
namespace Machine.NativePadEncryption
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

structure Input where
  pad : List Bool
  message : List Bool
  sameLength : pad.length = message.length

def cipher (input : Input) : List Bool := OneTimePad.xorList input.pad input.message

theorem cipher_length (input : Input) : (cipher input).length = input.message.length :=
  OneTimePad.xorList_length _ _ input.sameLength

def maskInput (input : Input) : FlaggedBlockXor.Contextual.Input :=
  {key := input.pad, message := input.message, sameLength := input.sameLength, outputSuffix := [none]}

noncomputable def masking : NativeComponent Input Configuration :=
  FlaggedBlockXor.Contextual.component.swapTapes.reindex maskInput

def eraseInput (input : Input) : NativeBackwardErasure.Input :=
  { bits := FlaggedBlockXor.request input.message ++ input.pad
    other := {left := (cipher input).reverse.map some, right := [none]} }

noncomputable def link : TypedNativeComposition.Link masking.procedure NativeBackwardErasure.component.procedure :=
  masking.link NativeBackwardErasure.component
    (fun _ machine => {machine.resumeAt 36 with halted := true}.swapTapes)
    (by
      intro input output h
      change output ∈ (PMF.pure (FlaggedBlockXor.Contextual.finish (maskInput input))).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun input _ => eraseInput input)
    (by
      intro input output h
      change output ∈ (PMF.pure (FlaggedBlockXor.Contextual.finish (maskInput input))).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun input => 4 * (FlaggedBlockXor.request input.message ++ input.pad).length + 3)
    (fun _ _ _ => Nat.le_refl _)

def fixedCode : Program := FlaggedBlockXor.code.swapTapes.followedBy eraseOutputBlock

theorem fixedCode_eq : fixedCode = link.code := rfl

theorem code_length : link.code.length = 45 := by
  rw [link.code_length]
  rfl

def initial (input : Input) : Configuration := (FlaggedBlockXor.Contextual.initial (maskInput input)).swapTapes

def publicExit (ciphertext : List Bool) : Configuration :=
  { pc := 44
    inputTape := {left := ciphertext.reverse.map some, right := [none]}
    outputTape := {right := List.replicate (3 * ciphertext.length + 2) none}
    halted := true }

def finish (input : Input) : Configuration := publicExit (cipher input)

@[simp] theorem publicExit_bits (ciphertext : List Bool) : (publicExit ciphertext).inputTape.bits = ciphertext := by
  simp [publicExit, Tape.bits]

theorem semantics (input : Input) : link.native.execution.semantics input = PMF.pure (finish input) := by
  rw [link.semantics]
  change (PMF.pure (FlaggedBlockXor.Contextual.finish (maskInput input))).bind _ = _
  rw [PMF.pure_bind]
  change (PMF.pure (NativeBackwardErasure.finish (eraseInput input))).map _ = _
  rw [PMF.pure_map]
  congr 1
  change (
    { pc := 44
      inputTape := (eraseInput input).other
      outputTape := {right := List.replicate ((FlaggedBlockXor.request input.message ++ input.pad).reverse.length + 1) none ++ []}
      halted := true } : Configuration) = finish input
  simp [eraseInput, finish, publicExit, cipher_length, FlaggedBlockXor.request_length, input.sameLength]
  omega

theorem budget (input : Input) : link.native.execution.budget input = 36 * input.message.length + 16 := by
  rw [link.budget]
  change 24 * input.message.length + 8 + (4 * (FlaggedBlockXor.request input.message ++ input.pad).length + 3) + 1 = _
  simp only [List.length_append, FlaggedBlockXor.request_length, input.sameLength]
  omega

theorem run (input : Input) (horizon : Nat) (hTime : 36 * input.message.length + 16 ≤ horizon) :
    evalConfigWithin link.code (initial input) horizon = PMF.pure (finish input) := by
  have h := link.run input horizon (by
    change link.native.execution.budget input ≤ horizon
    rw [budget]
    exact hTime)
  exact h.trans (semantics input)

theorem firstArrival_joint (input : Input) :
    link.component.firstArrival.procedure.execution.costed input = PMF.pure (finish input, 36 * input.message.length + 16) := by
  rw [link.firstArrival_costed_from_components]
  change (FlaggedBlockXor.Contextual.component.swapTapes.firstArrival.procedure.execution.costed (maskInput input)).bind
    (fun first => (NativeBackwardErasure.component.firstArrival.procedure.execution.costed (eraseInput input)).map
      (fun second => ({second.1.resumeAt link.finalPc with halted := true}, first.2 + second.2 + 1))) = _
  rw [FlaggedBlockXor.Contextual.component.swapTapes_firstArrival_costed,
    FlaggedBlockXor.Contextual.firstArrival_joint, PMF.pure_map, PMF.pure_bind,
    NativeBackwardErasure.firstArrival_joint, PMF.pure_map]
  have hFinish : { (NativeBackwardErasure.finish (eraseInput input)).resumeAt link.finalPc with halted := true } = finish input := by
    have h := semantics input
    rw [link.semantics] at h
    change (PMF.pure (FlaggedBlockXor.Contextual.finish (maskInput input))).bind _ = _ at h
    rw [PMF.pure_bind] at h
    change (PMF.pure (NativeBackwardErasure.finish (eraseInput input))).map _ = _ at h
    rw [PMF.pure_map] at h
    change PMF.pure { (NativeBackwardErasure.finish (eraseInput input)).resumeAt link.finalPc with halted := true } =
      PMF.pure (finish input) at h
    have hMem : { (NativeBackwardErasure.finish (eraseInput input)).resumeAt link.finalPc with halted := true } ∈
        (PMF.pure (finish input)).support := by rw [← h]; simp
    simpa only [PMF.mem_support_pure_iff] using hMem
  rw [hFinish]
  congr 1
  apply Prod.ext
  · rfl
  · change 24 * input.message.length + 8 + (4 * (FlaggedBlockXor.request input.message ++ input.pad).length + 3) + 1 = _
    simp only [List.length_append, FlaggedBlockXor.request_length, input.sameLength]
    omega

theorem initial_cells (input : Input) : (initial input).tapeCells = 4 * input.message.length + 5 := by
  rw [initial, Configuration.tapeCells_swapTapes, FlaggedBlockXor.Contextual.initial_cells]
  simp [maskInput]

def bitBound (size : Nat) : Nat := StructuredCodeEncoding.bound fixedCode 0 (4 * size + 5) (36 * size + 16)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 5))
    (((PolynomiallyBounded.const 36).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 16))

theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ 36 * input.message.length + 16)
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF link.code) elapsed (initial input)).support) :
    (StructuredCodeEncoding.completeEncoding.encode (link.code, state)).length ≤ bitBound input.message.length :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (by rw [initial_cells]) (Nat.le_refl _))

end Machine.NativePadEncryption
