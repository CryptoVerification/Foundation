import Foundation.Crypto.Semantics.Machine.FlaggedBlockXorContinuation
import Foundation.Crypto.Semantics.Machine.NativeTapeMove
import Foundation.Crypto.Semantics.Machine.NativeObservers
import Foundation.Crypto.Semantics.Machine.ResponseExport

/-! One native program masks an arbitrary-length equal-size operand pair,
moves the actual output head left and reads the last ciphertext bit. This
internal computation retains private input; it is not a public-game backend. -/
namespace Foundation.Examples.NativeMaskedLastBit
open Machine Foundation.Probability TimedExecution
open FlaggedBlockXor.Component (Input)
set_option backward.isDefEq.respectTransparency false

noncomputable def firstComponent : NativeComponent Configuration Configuration where
  procedure := NativeObservers.first
  closed := Program.controlClosed_step (by decide)
  entry := fun _ => by change 0 < 5; decide
  active := fun _ => rfl
  halted := NativeObservers.first_halted

noncomputable def maskMove := FlaggedBlockXor.Component.continueWith
  (NativeTapeMove.component .output true) (fun _ => rfl) (fun _ => 2) (fun _ => Nat.le_refl 2)

noncomputable def link := maskMove.append firstComponent (fun _ machine => machine)
  (by
    intro input output _
    change (output.resumeAt 0).rebasePc _ = output.resumeAt _
    simp [Configuration.resumeAt, Configuration.rebasePc])
  (fun _ => 3) (fun _ _ _ => Nat.le_refl 3)

def middle (input : Input) : Configuration :=
  {(NativeTapeMove.finish .output true (FlaggedBlockXor.final input.key input.message)).resumeAt 41 with halted := true}

def finish (input : Input) : Configuration :=
  {(NativeObservers.firstExit (middle input)).resumeAt 49 with halted := true}

theorem code : link.code =
    (FlaggedBlockXor.code.followedBy (NativeTapeMove.code .output true)).followedBy NativeObservers.firstCode := rfl

theorem code_length : link.code.length = 50 := by decide

theorem maskMove_budget (input : Input) : maskMove.native.execution.budget input = 24 * input.message.length + 11 := by
  dsimp only [maskMove]
  rw [FlaggedBlockXor.Component.continue_budget]

theorem budget (input : Input) : link.native.execution.budget input = 24 * input.message.length + 15 := by
  rw [TypedNativeComposition.Link.budget]
  change maskMove.native.execution.budget input + 3 + 1 = _
  rw [maskMove_budget]

theorem middle_semantics (input : Input) : maskMove.native.execution.semantics input = PMF.pure (middle input) := by
  dsimp only [maskMove]
  rw [FlaggedBlockXor.Component.continue_semantics]
  change (PMF.pure (NativeTapeMove.finish .output true (FlaggedBlockXor.final input.key input.message))).map _ = _
  rw [PMF.pure_map]
  rfl

theorem semantics (input : Input) : link.native.execution.semantics input = PMF.pure (finish input) := by
  rw [TypedNativeComposition.Link.semantics, middle_semantics, PMF.pure_bind]
  change (PMF.pure (NativeObservers.firstExit (middle input))).map _ = _
  rw [PMF.pure_map]
  rfl

theorem run (input : Input) (horizon : Nat) (hTime : 24 * input.message.length + 15 ≤ horizon) :
    evalConfigWithin link.code (FlaggedBlockXor.initial input.key input.message) horizon = PMF.pure (finish input) :=
  (link.run input horizon (by simpa only [← link.budget, budget] using hTime)).trans (semantics input)

theorem decision (input : Input) :
    (finish input).outputTape.current.getD false =
      (OneTimePad.xorList input.key input.message).getLast?.getD false := by
  change ((FlaggedBlockXor.final input.key input.message).outputTape.moveLeft.current.getD false) = _
  rw [FlaggedBlockXor.final_outputTape, List.getLast?_eq_head?_reverse]
  cases h : (OneTimePad.xorList input.key input.message).reverse <;> simp [Tape.moveLeft]

theorem retained_input (input : Input) :
    (finish input).inputTape = (FlaggedBlockXor.final input.key input.message).inputTape := rfl

noncomputable def spaceProfile : Nat → Nat :=
  link.storageProfile (fun _ => 0) (fun size => 3 * size + 3) (fun size => 24 * size + 11) (fun _ => 3)

theorem space_polynomial : PolynomiallyBounded spaceProfile :=
  link.storageProfile_polynomial (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 3))
    (((PolynomiallyBounded.const 24).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 11))
    (PolynomiallyBounded.const 3)

theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ 24 * input.message.length + 15)
    (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF link.code) elapsed
      (FlaggedBlockXor.initial input.key input.message)).support) :
    (NativeEncodedResources.completeEncoding.encode (link.code, target)).length ≤ spaceProfile input.message.length := by
  apply link.storage_profile (fun _ => 0) (fun size => 3 * size + 3)
    (fun size => 24 * size + 11) (fun _ => 3) (fun size value => value.message.length = size)
    _ _ _ _ input.message.length input rfl elapsed _ target hTarget
  · intro size value _
    exact Nat.le_refl 0
  · intro size value hSize
    change (FlaggedBlockXor.initial value.key value.message).tapeCells ≤ _
    simpa only [hSize] using FlaggedBlockXor.Component.initial_cells value
  · intro size value hSize
    rw [maskMove_budget]
    omega
  · intro size value _
    exact Nat.le_refl 3
  · change elapsed ≤ maskMove.native.execution.budget input + 3 + 1
    rw [maskMove_budget]
    omega

end Foundation.Examples.NativeMaskedLastBit
