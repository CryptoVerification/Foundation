import Foundation.Crypto.Semantics.Machine.NativeCleanEightBitCipher
import Foundation.Crypto.Semantics.Machine.NativeCiphertextToggle
import Foundation.Crypto.Semantics.Machine.NativeSequenceResultLaw
import Foundation.Crypto.Semantics.Probability.ObserverBound

/-! Concrete native continuations after physical history erasure.
The same linked execution runs cipher, cleanup, and caller; no state reload.
The generic contract requires actual stopping of the chosen caller on all tapes. -/
namespace Machine.NativeCleanCipherContinuation
open Foundation.Probability NativeUniformSequence
open scoped ENNReal
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

attribute [local irreducible] NativeControlledEightBitCipher.code

def code (caller : Program) : Program := NativeCleanEightBitCipher.code.followedBy caller

noncomputable def kernel (caller : Program) (T : ℕ) (inputSuffix outputSuffix : Tape)
    (result : Fin 5 × Bool) : PMF Configuration :=
  (evalConfigWithin caller
    ((NativeCleanEightBitCipher.finish 0 result inputSuffix outputSuffix).resumeAt 0) T).map
      (fun c => {c with pc := NativeCleanEightBitCipher.code.length + caller.length + 2, halted := true})

theorem run (caller : Program) (T : ℕ) (hCaller : StopsEverywhere caller T)
    (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code caller) (NativeControlledEightBitCipher.entry v message inputSuffix outputSuffix)
      (411 + T + 1) = (tableEightBitLaw v message).bind (kernel caller T inputSuffix outputSuffix) := by
  unfold code
  exact NativeSequenceResultLaw.run NativeCleanEightBitCipher.code caller 411 T
    NativeCleanEightBitCipher.stops hCaller _ _ (tableEightBitLaw v message)
    (fun result => NativeCleanEightBitCipher.finish
      (NativeCleanEightBitCipher.source.length + NativePrivateHistoryErasure.cleanup.length + 2)
      result inputSuffix outputSuffix)
    (fun result => (NativeCleanEightBitCipher.finish 0 result inputSuffix outputSuffix).resumeAt 0)
    (NativeCleanEightBitCipher.run v message inputSuffix outputSuffix)
    (fun result => NativeCleanEightBitCipher.finish_resume _ result inputSuffix outputSuffix)

theorem stops (caller : Program) (T : ℕ) (hCaller : StopsEverywhere caller T) :
    StopsEverywhere (code caller) (411 + T + 1) := by
  unfold code
  exact NativeUniformSequence.stops _ _ _ _ NativeCleanEightBitCipher.stops hCaller

theorem initial_observation {α : Type*} (caller : Program) (T : ℕ)
    (hCaller : StopsEverywhere caller T) (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d)
    (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin (code caller)
      (Configuration.initial (List.ofFn (EightBitCipherControl.request v message)))
      (411 + T + 1)).map observe =
      ((tableEightBitLaw v message).bind (kernel caller T {} {})).map observe := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeControlledCipherInitial.entry_equivalent v message).symm _ _ hObserve, run caller T hCaller]

theorem observer_bound (caller : Program) (T : ℕ) (hCaller : StopsEverywhere caller T)
    (left right : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape)
    (allowed : ((Fin 5 × Bool) → PMF Bool) → Prop) (epsilon : ℝ≥0∞)
    (bound : ObserverBound allowed (tableEightBitLaw left message) (tableEightBitLaw right message) epsilon)
    (observe : Configuration → Bool)
    (admitted : allowed (fun result => (kernel caller T inputSuffix outputSuffix result).map observe)) :
    probabilityGap
      (eventProb ((evalConfigWithin (code caller)
        (NativeControlledEightBitCipher.entry left message inputSuffix outputSuffix) (411 + T + 1)).map observe) (· = true))
      (eventProb ((evalConfigWithin (code caller)
        (NativeControlledEightBitCipher.entry right message inputSuffix outputSuffix) (411 + T + 1)).map observe) (· = true)) ≤ epsilon := by
  rw [run caller T hCaller, run caller T hCaller]
  simpa only [observerGap, PMF.bind_map, PMF.bind_bind, PMF.map_bind, PMF.bind_pure_comp] using bound _ admitted

theorem toggle_stops : StopsEverywhere (code NativeCiphertextToggle.code) 418 :=
  stops _ 6 NativeCiphertextToggle.stops

theorem toggle_run (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code NativeCiphertextToggle.code) (NativeControlledEightBitCipher.entry v message inputSuffix outputSuffix) 418 =
      (tableEightBitLaw v message).map (fun result => NativeCleanEightBitCipher.finish
        (NativeCleanEightBitCipher.code.length + NativeCiphertextToggle.code.length + 2)
        (result.1, !result.2) inputSuffix outputSuffix) := by
  rw [run _ 6 NativeCiphertextToggle.stops]
  unfold kernel
  have h (result : Fin 5 × Bool) :
      evalConfigWithin NativeCiphertextToggle.code
        ((NativeCleanEightBitCipher.finish 0 result inputSuffix outputSuffix).resumeAt 0) 6 =
        PMF.pure {pc := 7, inputTape := (NativeCleanEightBitCipher.finish 0 result inputSuffix outputSuffix).inputTape, outputTape := {outputSuffix with left := some (!result.2) :: outputSuffix.left}, halted := true} :=
    NativeCiphertextToggle.run _ outputSuffix result.2
  simp only [h, PMF.pure_map]
  rfl

theorem toggle_initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin (code NativeCiphertextToggle.code)
      (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 418).map
      NativeEightBitCipher.observe = (tableEightBitLaw v message).map
        (fun result => some (result.1, !result.2)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeControlledCipherInitial.entry_equivalent v message).symm 418 _
    NativeControlledCipherInitial.observe_equivalent, toggle_run, PMF.map_comp]
  congr 1
  funext result
  exact NativeCleanEightBitCipher.observe_finish _ (result.1, !result.2) {} {}

theorem toggle_haltsWithin (input : List Bool) :
    HaltsWithin (code NativeCiphertextToggle.code) input 418 :=
  toggle_stops (Tape.ofBits input) {}

def toggle_bounded : CryptoLogic.BoundedProgram where
  program := code NativeCiphertextToggle.code
  budget := fun _ => 418
  polynomial := PolynomiallyBounded.const 418
  halts := toggle_haltsWithin

theorem toggle_polynomial_time : PolynomialTime (code NativeCiphertextToggle.code) :=
  toggle_bounded.polynomialTime

end Machine.NativeCleanCipherContinuation
