import Foundation.Crypto.Semantics.Oracle.CallerRound
import Foundation.Crypto.Semantics.Oracle.CallerRuntimeInstances
import Foundation.Crypto.Semantics.Oracle.FreshMaskCallerService
import Foundation.Crypto.Semantics.Oracle.AdaptiveBitstringLoop

/-! One real round of the fixed five-instruction adaptive caller linked to
native fresh-key encryption. Counter updates, request capture/export,
component loading/computation/export and caller resumption are charged.
The caller's next request is the actual preceding ciphertext. -/
namespace CryptoOracle.Interactive.FreshMaskAdaptiveRound
open Machine Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {State : Type u} (oracle : BitOracle State)

noncomputable def runtime := CallerRuntime.packet FreshMaskCallerService.componentStep
  FreshMaskCallerService.begin FreshMaskCallerService.ready AdaptiveBitstringLoop.code oracle

noncomputable def service (retained : Unit) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :=
  FreshMaskCallerService.rawExecution AdaptiveBitstringLoop.code oracle caller state trace request

theorem service_entry (retained : Unit) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :
    (service oracle retained caller state trace request).entry () =
      (runtime oracle).request retained caller state trace request := by
  cases retained
  exact FreshMaskCallerService.raw_entry _ _ _ _ _ _

theorem service_exit (retained : Unit) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (output : Unit × Configuration State) :
    (service oracle retained caller state trace request).exit () output = (runtime oracle).source output := rfl

theorem selection_run (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (SourcePrefix.step AdaptiveBitstringLoop.code oracle) (2 * request.length + 5)
      (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace) =
      PMF.pure ⟨state, .awaiting (AdaptiveBitstringLoop.callMachine remaining past request).advance request, trace⟩ := by
  have hPrepare : TimedExecution.eval (SourcePrefix.step AdaptiveBitstringLoop.code oracle) 2
      (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace) =
      PMF.pure ⟨state, .running (AdaptiveBitstringLoop.callMachine remaining past request), trace⟩ := by
    cases remaining <;> simp [TimedExecution.eval, SourcePrefix.step, SourcePrefix.boundary,
      AdaptiveBitstringLoop.frame, AdaptiveBitstringLoop.machine, AdaptiveBitstringLoop.callMachine,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition,
      AdaptiveBitstringLoop.code, Machine.Instruction.next, Machine.Configuration.tape,
      Machine.Configuration.updateTape, Machine.Configuration.advance, Tape.ofBits, Tape.moveRight,
      List.replicate_succ, PMF.pure_map]
  rw [show 2 * request.length + 5 = 2 + (2 * request.length + 3) by omega, TimedExecution.eval_add,
    hPrepare, PMF.pure_bind]
  exact SourcePrefix.capture_run AdaptiveBitstringLoop.code oracle
    (AdaptiveBitstringLoop.callMachine remaining past request) state trace request [] [] rfl rfl (by
      rfl)

noncomputable def selection (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    SourcePrefix.Input AdaptiveBitstringLoop.code oracle where
  start := AdaptiveBitstringLoop.frame state (remaining + 1) past request trace
  budget := 2 * request.length + 5
  complete := by
    intro frame hFrame
    rw [selection_run, PMF.mem_support_pure_iff] at hFrame
    subst frame
    rfl

private theorem service_bound (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool))
    (frame : Configuration State)
    (hFrame : frame ∈ (TimedExecution.eval (SourcePrefix.step AdaptiveBitstringLoop.code oracle)
      (selection oracle state remaining past request trace).budget
      (selection oracle state remaining past request trace).start).support)
    (caller : Machine.Configuration) (chosen : List Bool) (hChosen : frame.control = .awaiting caller chosen) :
    (service oracle () caller frame.state frame.reverseTrace chosen).budget () ≤ 70 * request.length + 51 := by
  change frame ∈ (TimedExecution.eval (SourcePrefix.step AdaptiveBitstringLoop.code oracle)
    (2 * request.length + 5) (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace)).support at hFrame
  rw [selection_run, PMF.mem_support_pure_iff] at hFrame
  subst frame
  cases hChosen
  rw [service, FreshMaskCallerService.raw_budget]

noncomputable def invocation (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :=
  (runtime oracle).roundAt (service oracle) (service_entry oracle) (service_exit oracle) ()
    (selection oracle state remaining past request trace) (70 * request.length + 51)
    (service_bound oracle state remaining past request trace)

theorem invocation_budget (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (invocation oracle state remaining past request trace).budget () = 72 * request.length + 57 := by
  change (2 * request.length + 5) + (1 + (70 * request.length + 51)) = _
  omega

theorem invocation_semantics (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (invocation oracle state remaining past request trace).semantics () =
      (uniform (Bits request.length)).map (fun ciphertext =>
        ((), NativeCallback.resumed (AdaptiveBitstringLoop.callMachine remaining past request).advance
          state trace request ciphertext.toList)) := by
  rw [invocation, CallerRuntime.Runtime.roundAt_semantics]
  change (TimedExecution.eval (SourcePrefix.step AdaptiveBitstringLoop.code oracle)
    (2 * request.length + 5) (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace)).bind _ = _
  rw [selection_run, PMF.pure_bind, CallerRuntime.Runtime.response_semantics]
  exact FreshMaskCallerService.raw_semantics _ _ _ _ _ _

def responseBits (output : Unit × Configuration State) : List Bool :=
  match output.2.control with
  | .running machine => machine.outputBits
  | _ => []

private theorem responseBits_resumed (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request packet : List Bool) :
    responseBits ((), NativeCallback.resumed caller state trace request packet) = packet := by
  have h := (NativePacketService.loaded_equivalent packet).2.2.2.bits
  change (ResponseLoading.loaded packet).bits = (Tape.ofBits packet).bits at h
  simpa only [responseBits, NativeCallback.resumed, Machine.Configuration.outputBits, Tape.bits_ofBits] using h

noncomputable def packet (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :=
  (invocation oracle state remaining past request trace).observe responseBits
    (fun _ packet => (runtime oracle).embed ()
      (NativeCallback.resumed (AdaptiveBitstringLoop.callMachine remaining past request).advance state trace request packet))
    (by
      intro _ output hOutput
      rw [invocation_semantics, PMF.mem_support_map_iff] at hOutput
      obtain ⟨ciphertext, _, rfl⟩ := hOutput
      rw [responseBits_resumed]
      rfl)

noncomputable def suffix (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    Procedure (runtime oracle).step (List Bool) Unit :=
  TimedExecution.Procedure.ofFixed _
    (fun packet => (runtime oracle).embed ()
      (NativeCallback.resumed (AdaptiveBitstringLoop.callMachine remaining past request).advance state trace request packet))
    (fun packet _ => (runtime oracle).embed ()
      (AdaptiveBitstringLoop.frame state remaining (some true :: past) packet ((request, packet) :: trace)))
    (fun _ => PMF.pure ()) (fun _ => 1) (fun packet => by
      simp [TimedExecution.eval, runtime, CallerRuntime.packet, PacketResponseSource.step,
        NativeCallback.resumed, AdaptiveBitstringLoop.frame, AdaptiveBitstringLoop.callMachine,
        AdaptiveBitstringLoop.machine, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, AdaptiveBitstringLoop.code,
        Machine.Instruction.next, Machine.Configuration.advance, PMF.pure_map])

noncomputable def round (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :=
  ((packet oracle state remaining past request trace).seq
    (suffix oracle state remaining past request trace) (fun _ _ _ => rfl)
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)).observe Prod.fst
    (fun _ packet => (runtime oracle).embed ()
      (AdaptiveBitstringLoop.frame state remaining (some true :: past) packet ((request, packet) :: trace)))
    (fun _ _ _ => rfl)

theorem round_entry (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (round oracle state remaining past request trace).entry () =
      (runtime oracle).embed () (AdaptiveBitstringLoop.frame state (remaining + 1) past request trace) := rfl

theorem round_exit (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) (packet : List Bool) :
    (round oracle state remaining past request trace).exit () packet = (runtime oracle).embed ()
      (AdaptiveBitstringLoop.frame state remaining (some true :: past) packet ((request, packet) :: trace)) := rfl

theorem round_budget (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (round oracle state remaining past request trace).budget () = 72 * request.length + 58 := by
  change (invocation oracle state remaining past request trace).budget () + 1 = _
  rw [invocation_budget]

theorem round_semantics (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (round oracle state remaining past request trace).semantics () =
      (uniform (Bits request.length)).map Bits.toList := by
  simp only [round, packet, TimedExecution.Procedure.observe, TimedExecution.Procedure.seq, suffix, TimedExecution.Procedure.ofFixed,
    PMF.map_bind, PMF.pure_map, PMF.bind_pure]
  change ((invocation oracle state remaining past request trace).semantics ()).map responseBits = _
  rw [invocation_semantics, PMF.map_comp]
  congr 1
  funext ciphertext
  exact responseBits_resumed _ _ _ _ _

end CryptoOracle.Interactive.FreshMaskAdaptiveRound
