import Foundation.Crypto.Semantics.Oracle.OneUseProgramContract
import Foundation.Crypto.Semantics.Oracle.OneUseBitInitialization
import Foundation.Crypto.Semantics.Oracle.InitializationContinuation
import Foundation.Crypto.Semantics.Oracle.ControllerResourceEnvelope
import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.Asymptotic.PolynomiallyBounded

/-! Native uniform bit-key generation followed by a proved whole finite
caller program. Generation and consumer durations remain jointly distributed;
terminal evidence, not fuel exhaustion, justifies the final run law. -/
namespace CryptoOracle.Interactive.OneUseProgramInitialization
open Foundation.Probability Foundation.Symmetric TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def store {width : Nat} (key : Bits width) : Machine.Tape :=
  Machine.PairPreparation.operand [] key.toList []

variable (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Configuration State) (width : Nat)
    (consumers : ∀ key : Bits width, OneUseProgramContract.Consumer native code oracle caller (store key))
    (cap : Nat) (hCap : ∀ key, (consumers key).execution.budget () ≤ cap)

noncomputable def continuation := Procedure.dispatch (fun key => (consumers key).execution)

noncomputable def complete :=
  OneUseInitialization.follow Machine.OneTimePad.keygen native code oracle caller
    (OneUseBitInitialization.initialization native code oracle caller width) store (fun _ _ _ => rfl)
    (continuation native code oracle caller width consumers)
    (fun key => (consumers key).entry) (fun _ => cap) (fun _ result _ => hCap result.1)

theorem budget :
    (complete native code oracle caller width consumers cap hCap).budget () = 6 * width + 5 + cap := by
  rw [complete, OneUseInitialization.follow_budget, OneUseBitInitialization.budget]

theorem semantics :
    (complete native code oracle caller width consumers cap hCap).semantics () =
      (uniform (Bits width)).bind (fun key =>
        ((consumers key).execution.semantics ()).map (fun output => ((key, ()), output))) := by
  rw [complete, OneUseInitialization.follow_semantics]
  simp only [OneUseBitInitialization.initialization, OneUseInitialization.semantics,
    Machine.PrivateBitGeneration.native, Machine.Procedure.ofFixed, TimedExecution.Procedure.ofFixed,
    PMF.bind_map, continuation, Procedure.dispatch, Function.comp_def]

/-- The complete caller exit is retained, including its physical private
store. Generated-key metadata is not substituted for an actual machine tape. -/
theorem exit (result : (Bits width × Unit) × OneUseSource.Control State) :
    (complete native code oracle caller width consumers cap hCap).exit () result = .active result.2 := by
  change OneUseInitialization.Control.active ((consumers result.1.1).execution.exit () result.2) = _
  rw [(consumers result.1.1).exit]

include hCap in
/-- Whole execution after native key generation, at any horizon above the
composed cap. Every supported consumer return must be a genuine terminal. -/
theorem run (horizon : Nat) (hBudget : 6 * width + 5 + cap ≤ horizon) :
    TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen native code oracle caller)
      horizon (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      (uniform (Bits width)).bind (fun key =>
        ((consumers key).execution.semantics ()).map OneUseInitialization.Control.active) := by
  have h := (complete native code oracle caller width consumers cap hCap).final_run ()
    (fun result hs => by
      rw [semantics, PMF.mem_support_bind_iff] at hs
      obtain ⟨key, _, hs⟩ := hs
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨output, hOutput, he⟩ := hs
      subst result
      rw [exit]
      change (OneUseSource.step native code oracle output).map OneUseInitialization.Control.active = _
      rw [OneUseProgramContract.absorbing native code oracle output ((consumers key).stops output hOutput), PMF.pure_map])
    horizon (by rw [budget]; exact hBudget)
  rw [semantics, PMF.map_bind] at h
  simp only [PMF.map_comp, exit, Function.comp_def] at h
  exact h

/-- Arbitrary residual execution retains the actual initialization/caller
cost correlation. This law does not require replacing actual times by caps. -/
theorem costed :
    (complete native code oracle caller width consumers cap hCap).costed () =
      ((OneUseBitInitialization.initialization native code oracle caller width).costed ()).bind
        (fun generated => ((consumers generated.1.1).execution.costed ()).map
          (fun returned => ((generated.1, returned.1), generated.2 + returned.2))) := rfl

theorem resume (horizon : Nat) (hBudget : 6 * width + 5 + cap ≤ horizon) :
    TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen native code oracle caller)
      horizon (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      ((complete native code oracle caller width consumers cap hCap).costed ()).bind (fun result =>
        TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen native code oracle caller)
          (horizon - result.2) (.active result.1.2)) := by
  have h := (complete native code oracle caller width consumers cap hCap).law () horizon
    (by rw [budget]; exact hBudget)
  simp only [exit] at h
  exact h

/-- Include generation, private-store transfer, every consumer instruction,
all request/response copies, and the caller's original tapes and transcript. -/
theorem memory_peak (stateSize : State → Nat) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request answer, answer ∈ (oracle state request).support →
      stateSize answer.1 ≤ stateSize state + stateIncrement ∧ answer.2.length ≤ responseCap)
    (elapsed : Nat) (hElapsed : elapsed ≤ 6 * width + 5 + cap)
    (target : OneUseInitialization.Control State)
    (h : target ∈ (TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen native code oracle caller) elapsed
      (.initializing (.generating (Machine.Configuration.initial (List.replicate width true))))).support) :
    ControllerStorage.initializationCells stateSize caller target ≤
      4 * (ControllerExtent.initializationExtent stateSize caller
        (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) +
        (6 * width + 5 + cap) * (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (ControllerExtent.initializationExtent stateSize caller
        (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) +
        (6 * width + 5 + cap) * (stateIncrement + responseCap + 2)) + 2 :=
  ControllerExtent.initialization_peak stateSize Machine.OneTimePad.keygen native code oracle caller
    stateIncrement responseCap hOracle (6 * width + 5 + cap) elapsed hElapsed
    (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) target h

theorem time_profile_polynomial {width cap : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hCap : PolynomiallyBounded cap) :
    PolynomiallyBounded (fun n => 6 * width n + 5 + cap n) :=
  (((PolynomiallyBounded.const 6).mul hWidth).add (PolynomiallyBounded.const 5)).add hCap

theorem memory_profile_polynomial {initialExtent width cap increment : Nat → Nat}
    (hInitial : PolynomiallyBounded initialExtent) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hIncrement : PolynomiallyBounded increment) :
    PolynomiallyBounded (fun n =>
      4 * (initialExtent n + (6 * width n + 5 + cap n) * increment n) ^ 2 +
      11 * (initialExtent n + (6 * width n + 5 + cap n) * increment n) + 2) := by
  have he := hInitial.add ((time_profile_polynomial hWidth hCap).mul hIncrement)
  have hb := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 11).mul he)).add (PolynomiallyBounded.const 2)
  simpa only [pow_two] using hb

end CryptoOracle.Interactive.OneUseProgramInitialization
