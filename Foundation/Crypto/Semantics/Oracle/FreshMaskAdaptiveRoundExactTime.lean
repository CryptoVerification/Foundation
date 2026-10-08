import Foundation.Crypto.Semantics.Oracle.FreshMaskAdaptiveRound
import Foundation.Crypto.Semantics.Oracle.SourcePrefixExactTime
import Foundation.Crypto.Semantics.Oracle.CallerRoundCosted
import Foundation.Crypto.Semantics.Oracle.FreshMaskCallerServiceExactTime

/-! First selection time and the joint invocation cost for the adaptive
native caller. The next request is still the actual preceding ciphertext. -/
namespace CryptoOracle.Interactive.FreshMaskAdaptiveRound
open Machine Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {State : Type u} (oracle : BitOracle State)

theorem selection_before (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (SourcePrefix.step AdaptiveBitstringLoop.code oracle) (2 * request.length + 4)
      (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace) =
      PMF.pure ⟨state, .reversing (AdaptiveBitstringLoop.callMachine remaining past request).advance [] request, trace⟩ := by
  have hPrepare : TimedExecution.eval (SourcePrefix.step AdaptiveBitstringLoop.code oracle) 2
      (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace) =
      PMF.pure ⟨state, .running (AdaptiveBitstringLoop.callMachine remaining past request), trace⟩ := by
    cases remaining <;> simp [TimedExecution.eval, SourcePrefix.step, SourcePrefix.boundary,
      AdaptiveBitstringLoop.frame, AdaptiveBitstringLoop.machine, AdaptiveBitstringLoop.callMachine,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition,
      AdaptiveBitstringLoop.code, Machine.Instruction.next, Machine.Configuration.tape,
      Machine.Configuration.updateTape, Machine.Configuration.advance, Tape.ofBits, Tape.moveRight,
      List.replicate_succ, PMF.pure_map]
  rw [show 2 * request.length + 4 = 2 + (2 * request.length + 2) by omega, TimedExecution.eval_add,
    hPrepare, PMF.pure_bind]
  exact SourcePrefix.capture_before AdaptiveBitstringLoop.code oracle
    (AdaptiveBitstringLoop.callMachine remaining past request) state trace request [] [] rfl rfl rfl

theorem selection_first_joint (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    runToBoundary (SourcePrefix.step AdaptiveBitstringLoop.code oracle) SourcePrefix.boundary
      (2 * request.length + 5) (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace) =
      PMF.pure (⟨state, .awaiting (AdaptiveBitstringLoop.callMachine remaining past request).advance request, trace⟩,
        2 * request.length + 5) := by
  have hb := selection_before oracle state remaining past request trace
  have ha := selection_run oracle state remaining past request trace
  have h := runToBoundary_joint_of_adjacent (SourcePrefix.step AdaptiveBitstringLoop.code oracle)
    SourcePrefix.boundary (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace)
    (2 * request.length + 4) (fun frame hf => by simp [SourcePrefix.step, hf])
    (by
      intro frame hf
      rw [hb, PMF.mem_support_pure_iff] at hf
      subst frame; rfl)
    (by
      intro frame hf
      rw [show 2 * request.length + 4 + 1 = 2 * request.length + 5 by omega, ha,
        PMF.mem_support_pure_iff] at hf
      subst frame; rfl)
  simpa only [show 2 * request.length + 4 + 1 = 2 * request.length + 5 by omega,
    ha, PMF.pure_map] using h

theorem invocation_costed (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (invocation oracle state remaining past request trace).costed () =
      (uniform (Bits request.length)).map (fun ciphertext =>
        (((), NativeCallback.resumed (AdaptiveBitstringLoop.callMachine remaining past request).advance
          state trace request ciphertext.toList), 72 * request.length + 57)) := by
  rw [invocation, CallerRuntime.Runtime.roundAt_costed]
  change (runToBoundary (SourcePrefix.step AdaptiveBitstringLoop.code oracle) SourcePrefix.boundary
    (2 * request.length + 5) (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace)).bind _ = _
  rw [selection_first_joint, PMF.pure_bind, CallerRuntime.Runtime.response_costed]
  change (((FreshMaskCallerService.rawExecution AdaptiveBitstringLoop.code oracle
    (AdaptiveBitstringLoop.callMachine remaining past request).advance state trace request).costed ()).map _).map _ = _
  rw [FreshMaskCallerService.raw_costed_uniform, PMF.map_comp, PMF.map_comp]
  congr 1
  funext ciphertext
  dsimp only [Function.comp_def]
  congr 1
  omega

/-- The final native jump adds one transition to each invocation. -/
theorem round_costed (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (round oracle state remaining past request trace).costed () =
      (uniform (Bits request.length)).map
        (fun ciphertext => (ciphertext.toList, 72 * request.length + 58)) := by
  simp only [round, packet, TimedExecution.Procedure.observe, TimedExecution.Procedure.seq,
    suffix, TimedExecution.Procedure.ofFixed, PMF.map_bind, PMF.pure_map, PMF.pure_bind,
    PMF.map_comp, Function.comp_def]
  rw [invocation_costed]
  simp only [PMF.bind_map, PMF.pure_bind, PMF.bind_pure, PMF.map_comp, Function.comp_def]
  congr 1
  funext ciphertext
  have hb := (NativePacketService.loaded_equivalent ciphertext.toList).2.2.2.bits
  change (ResponseLoading.loaded ciphertext.toList).bits = (Tape.ofBits ciphertext.toList).bits at hb
  have hr : responseBits ((), NativeCallback.resumed
      (AdaptiveBitstringLoop.callMachine remaining past request).advance state trace request ciphertext.toList) =
      ciphertext.toList := by
    simpa only [responseBits, NativeCallback.resumed, Machine.Configuration.outputBits, Tape.bits_ofBits] using hb
  simp only [hr]
  rfl

end CryptoOracle.Interactive.FreshMaskAdaptiveRound
