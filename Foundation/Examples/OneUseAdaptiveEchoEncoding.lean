import Foundation.Examples.OneUseAdaptiveEcho
import Foundation.Crypto.Semantics.Oracle.PrivateEncodedStorage

/-! Full finite-program and private-runtime bit bounds for the actual
arbitrary-width adaptive echo example, including native key generation. -/
namespace Foundation.OneUseAdaptiveEchoExamples
open Foundation.Probability Foundation.Symmetric CryptoOracle.Interactive
universe u
variable {State : Type u}

noncomputable def encodedBudget (width : Nat) (input : List Bool) (state : State)
    (trace : List (List Bool × List Bool)) (stateSize : State → Nat) (stateIncrement responseCap : Nat) : Nat :=
  PrivateControllerEncoding.encodedBound Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code code
    0 (uniformExtent width input state trace stateSize)
    (105 * width + 99 * uniformExtent width input state trace stateSize + 305) stateIncrement responseCap

theorem initialized_encoded_peak {width : Nat} (message : Bits width) (input : List Bool) (state : State)
    (trace : List (List Bool × List Bool)) (stateSize : State → Nat) (E : Machine.FiniteBitEncoding State)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ start request result, result ∈ (oracle start request).support →
      stateSize result.1 ≤ stateSize start + stateIncrement ∧ result.2.length ≤ responseCap)
    (elapsed : Nat) (hElapsed : elapsed ≤ 105 * width + 99 * uniformExtent width input state trace stateSize + 305)
    (target : OneUseInitialization.Control State)
    (hTarget : target ∈ (TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen
      Machine.OneTimePad.Prepared.listProcedure.code code oracle (initial message input state trace).frame)
      elapsed (.initializing (.generating (Machine.Configuration.initial (List.replicate width true))))).support) :
    ((PrivateControllerEncoding.completeEncoding E).encode
      (Machine.OneTimePad.keygen, Machine.OneTimePad.Prepared.listProcedure.code, code,
        PrivateControllerEncoding.runtime (initial message input state trace).frame target)).length ≤
      encodedBudget width input state trace stateSize stateIncrement responseCap := by
  have hp := PrivateControllerEncoding.encoded_peak E stateSize hState Machine.OneTimePad.keygen
    Machine.OneTimePad.Prepared.listProcedure.code code oracle (initial message input state trace).frame
    stateIncrement responseCap hOracle _ elapsed hElapsed
    (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) target hTarget
  have hAddress : PrivateControllerEncoding.initializationMaxPc (initial message input state trace).frame
      (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) = 0 := rfl
  rw [hAddress] at hp
  exact hp.trans (PrivateControllerEncoding.encodedBound_mono_initial _ _ _ (Nat.le_refl _)
    (initial_extent_le_uniform message input state trace stateSize) _ _ _)

theorem encodedBudget_polynomial (stateSize : State → Nat)
    {width : Nat → Nat} {input : Nat → List Bool} {state : Nat → State}
    {trace : Nat → List (List Bool × List Bool)} {stateIncrement responseCap : Nat → Nat}
    (hWidth : PolynomiallyBounded width)
    (hExtent : PolynomiallyBounded (fun n => uniformExtent (width n) (input n) (state n) (trace n) stateSize))
    (hIncrement : PolynomiallyBounded stateIncrement) (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => encodedBudget (width n) (input n) (state n) (trace n) stateSize
      (stateIncrement n) (responseCap n)) :=
  PrivateControllerEncoding.encodedBound_polynomial _ _ _ (PolynomiallyBounded.const 0) hExtent
    (initialized_time_profile_polynomial hWidth hExtent) hIncrement hResponse

end Foundation.OneUseAdaptiveEchoExamples
