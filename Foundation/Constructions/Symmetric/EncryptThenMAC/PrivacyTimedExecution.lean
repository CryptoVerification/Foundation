import Foundation.Crypto.Semantics.TimedExecution
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyResponseLayout

/-! Actual-duration blocks for the concrete privacy controller. Source
resumption is an intermediate boundary, not an absorbing target state. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability
namespace Timing

universe u

theorem eval_eq (code : Source.Code) (oracle : CryptoOracle.Interactive.BitOracle State)
    (fuel : Nat) (start : Frame State) :
    Foundation.Probability.TimedExecution.eval (step code oracle) fuel start = eval code oracle fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      simp only [Foundation.Probability.TimedExecution.eval, eval]
      congr 1
      funext next
      exact ih next

def sourceBoundary (frame : Frame State) : Bool :=
  match frame.control with
  | .source _ _ => true
  | _ => false

noncomputable def sourceBlock (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (fuel : Nat) (start : Frame State) :=
  Foundation.Probability.TimedExecution.Block.stopped (step code oracle) sourceBoundary fuel start

/-- Every later ordinary evaluation resumes with the actual remaining
budget. The source machine is never padded at its resumption boundary. -/
theorem sourceBlock_law (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (fuel horizon : Nat)
    (start : Frame State) (h : fuel ≤ horizon) :
    eval code oracle horizon start = (sourceBlock code oracle fuel start).outcome.bind
      (fun result => eval code oracle (horizon - result.2) result.1) := by
  simpa only [eval_eq] using (sourceBlock code oracle fuel start).law horizon h

/-- The previously proved cell-level return certifies real completion of
this stopped block, for both successful and failed native output layouts. -/
theorem return_completes {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (storedKey : Tape)
    (key : TableMAC.Key width) (ciphertext : Option Bool) (machine : Configuration)
    (request : List Bool) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    (sourceBlock code oracle (returnBudget width ciphertext)
      ⟨state, .rewinding storedKey machine request
        (AuthenticateResponse.responseTape key ciphertext), sourceTrace, externalTrace⟩).Completes
      sourceBoundary := by
  intro result hResult
  apply Foundation.Probability.TimedExecution.runToBoundary_completes (step code oracle) sourceBoundary _ _ _ result hResult
  intro final hFinal
  rw [eval_eq, return_authentication_run, PMF.mem_support_pure_iff] at hFinal
  subst final
  rfl

noncomputable def haltBlock (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (fuel : Nat) (start : Frame State) :=
  Foundation.Probability.TimedExecution.Block.stopped (step code oracle) (fun frame => terminal frame.control) fuel start

theorem haltBlock_completes (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (fuel : Nat) (start : Frame State)
    (h : HaltsWithin code oracle start fuel) :
    (haltBlock code oracle fuel start).Completes (fun frame => terminal frame.control) := by
  intro result hResult
  apply Foundation.Probability.TimedExecution.runToBoundary_completes (step code oracle) (fun frame => terminal frame.control)
    fuel start _ result hResult
  simpa only [eval_eq, HaltsWithin] using h

/-- Final source termination, unlike source resumption, is absorbing and
therefore permits discarding residual execution. -/
theorem haltBlock_final_law (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (fuel horizon : Nat) (start : Frame State)
    (h : HaltsWithin code oracle start fuel) (hHorizon : fuel ≤ horizon) :
    eval code oracle horizon start = (haltBlock code oracle fuel start).outcome.map Prod.fst := by
  have hComplete := haltBlock_completes code oracle fuel start h
  simpa only [eval_eq] using (haltBlock code oracle fuel start).final_law
    (fun result hResult => step_terminal code oracle result.1 (hComplete result hResult))
    horizon hHorizon

end Timing
end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
