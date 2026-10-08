import Foundation.Examples.RetainedResponseCallback
import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableResponseCertified
import Foundation.Crypto.Semantics.ProcedureIteration

/-! Two complete adaptive requests in one actual reusable runtime. Both
requests run the retained-key copy and three-instruction acknowledgement
handler; the second request is the first reply. This is an execution witness,
not a cryptographic safety claim for the acknowledgement protocol. -/
namespace Foundation.Examples.ReusableResponseTwoQueries
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
open ResponseHandoffProgram
universe u
set_option backward.isDefEq.respectTransparency false

abbrev native := RetainedResponseCallback.native

def code : Code := [.call, .call, .native .halt]

variable {State : Type u} (oracle : BitOracle State) (key : List Bool)
    (state : State) (trace : List (List Bool × List Bool))

noncomputable def invocation (caller : Machine.Configuration) (request : List Bool) :=
  ReusableResponse.Certified.whole native code oracle caller state trace request key request
    (RetainedResponseCallback.handler key request).execution rfl
    (fun _ => ()) (fun _ => rfl) (fun _ => [false]) (fun _ => rfl) (fun _ => rfl)
    1 (fun _ _ => Nat.le_refl _)

noncomputable def sourceService (caller : Machine.Configuration) (request : List Bool) :=
  ReusableResponse.Certified.sourceService native code oracle caller state trace key request
    (RetainedResponseCallback.handler key request).execution rfl
    (fun _ => ()) (fun _ => rfl) (fun _ => [false]) (fun _ => rfl) (fun _ => rfl)
    1 (fun _ _ => Nat.le_refl _)

noncomputable def body (caller : Machine.Configuration) (request : List Bool) :=
  (sourceService oracle key state trace caller request).observe (fun _ => ())
    (fun _ _ => ReusableResponseSource.Control.source (retainedKey key)
      (NativeCallback.resumed caller state trace request [false]))
    (by
      intro _ result h
      rw [sourceService, ReusableResponse.Certified.sourceService_semantics] at h
      change result ∈ ((PMF.pure ()).map _).support at h
      rw [PMF.pure_map, PMF.mem_support_pure_iff] at h
      subst result
      rfl)

theorem body_budget (caller : Machine.Configuration) (request : List Bool) :
    (body oracle key state trace caller request).budget () = 9 * key.length + 3 * request.length + 26 := by
  change (sourceService oracle key state trace caller request).budget () = _
  rw [sourceService, ReusableResponse.Certified.sourceService_budget]
  change 9 * key.length + 3 * request.length + 3 + 6 * 1 + 17 = _
  omega

theorem body_semantics (caller : Machine.Configuration) (request : List Bool) :
    (body oracle key state trace caller request).semantics () = PMF.pure () := by
  change ((sourceService oracle key state trace caller request).semantics ()).map (fun _ => ()) = _
  rw [sourceService, ReusableResponse.Certified.sourceService_semantics]
  change ((PMF.pure ()).map _).map _ = _
  simp only [PMF.pure_map]

theorem body_semantics_all (caller : Machine.Configuration) (request : List Bool) (argument : Unit) :
    (body oracle key state trace caller request).semantics argument = PMF.pure () := by
  cases argument
  exact body_semantics oracle key state trace caller request

noncomputable def capture (caller : Machine.Configuration) (request : List Bool)
    (hActive : caller.halted = false) (hCall : code[caller.pc]? = some .call)
    (hTape : caller.outputTape = RequestExport.packetTape [] [] request) :=
  Procedure.ofFixed (ReusableResponse.step native code oracle)
    (fun _ : Unit => ReusableResponseSource.Control.source (retainedKey key) ⟨state, .running caller, trace⟩)
    (fun _ _ : Unit => .processing caller.advance state trace request (.headerWriting (retainedKey key) request {}))
    (fun _ => PMF.pure ()) (fun _ => 2 * request.length + 4)
    (fun _ => by simpa only [PMF.pure_map] using
      (ReusableResponse.capture_run native code oracle (retainedKey key) caller state trace request [] [] hActive hCall hTape))

noncomputable def query (caller : Machine.Configuration) (request : List Bool)
    (hActive : caller.halted = false) (hCall : code[caller.pc]? = some .call)
    (hTape : caller.outputTape = RequestExport.packetTape [] [] request) :=
  (capture oracle key state trace caller request hActive hCall hTape).seq
    (body oracle key state trace caller.advance request) (fun _ _ _ => rfl)
    (fun _ => 9 * key.length + 3 * request.length + 26)
    (fun _ _ _ => by rw [body_budget])

theorem query_budget (caller : Machine.Configuration) (request : List Bool)
    (hActive : caller.halted = false) (hCall : code[caller.pc]? = some .call)
    (hTape : caller.outputTape = RequestExport.packetTape [] [] request) :
    (query oracle key state trace caller request hActive hCall hTape).budget () =
      9 * key.length + 5 * request.length + 30 := by
  change (2 * request.length + 4) + (9 * key.length + 3 * request.length + 26) = _
  omega

def caller (request : List Bool) : Machine.Configuration :=
  { outputTape := ResponseLoading.loaded request }

def afterFirst (request : List Bool) : Machine.Configuration :=
  { (caller request).advance with outputTape := ResponseLoading.loaded [false] }

noncomputable def first (request : List Bool) :=
  query oracle key state trace (caller request) request rfl rfl (by rfl)

noncomputable def second (request : List Bool) :=
  query oracle key state ((request, [false]) :: trace) (afterFirst request) [false] rfl rfl (by rfl)

noncomputable def pair (request : List Bool) :=
  (first oracle key state trace request).seq
    ((second oracle key state trace request).reindex (fun _ : Unit × Unit => ()))
    (fun _ _ _ => rfl) (fun _ => 9 * key.length + 35)
    (fun _ _ _ => by
      change (second oracle key state trace request).budget () ≤ _
      rw [second, query_budget]
      simp)

def finalCaller (request : List Bool) : Machine.Configuration :=
  { (afterFirst request).advance with outputTape := ResponseLoading.loaded [false], halted := true }

def finalTrace (request : List Bool) := ([false], [false]) :: (request, [false]) :: trace

noncomputable def finish (request : List Bool) :=
  Procedure.ofFixed (ReusableResponse.step native code oracle)
    (fun _ : Unit => ReusableResponseSource.Control.source (retainedKey key)
      (NativeCallback.resumed (afterFirst request).advance state ((request, [false]) :: trace) [false] [false]))
    (fun _ _ : Unit => ReusableResponseSource.Control.source (retainedKey key)
      ⟨state, .running (finalCaller request), finalTrace trace request⟩)
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by
      simp [TimedExecution.eval, ReusableResponse.step, ReusableResponseSource.step, NativeCallback.resumed,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition,
        code, afterFirst, caller, finalCaller, finalTrace, Machine.Configuration.advance, Machine.Instruction.next,
        PMF.pure_map])

noncomputable def whole (request : List Bool) :=
  (pair oracle key state trace request).seq
    ((finish oracle key state trace request).reindex (fun _ : (Unit × Unit) × (Unit × Unit) => ()))
    (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem budget (request : List Bool) :
    (whole oracle key state trace request).budget () = 18 * key.length + 5 * request.length + 66 := by
  change (first oracle key state trace request).budget () + (9 * key.length + 35) + 1 = _
  rw [first, query_budget]
  omega

theorem semantics (request : List Bool) :
    (whole oracle key state trace request).semantics () = PMF.pure ((((), ()), ((), ())), ()) := by
  simp [whole, pair, first, second, query, capture, finish, Procedure.seq, Procedure.reindex, TimedExecution.Procedure.ofFixed,
    body_semantics_all, PMF.pure_map]

theorem run (request : List Bool) (horizon : Nat)
    (hBudget : 18 * key.length + 5 * request.length + 66 ≤ horizon) :
    TimedExecution.eval (ReusableResponse.step native code oracle) horizon
      (.source (retainedKey key) ⟨state, .running (caller request), trace⟩) =
      PMF.pure (.source (retainedKey key) ⟨state, .running (finalCaller request), finalTrace trace request⟩) := by
  have h := (whole oracle key state trace request).final_run () (by
    intro output hOutput
    change ReusableResponse.step native code oracle
      (.source (retainedKey key) ⟨state, .running (finalCaller request), finalTrace trace request⟩) =
      PMF.pure (.source (retainedKey key) ⟨state, .running (finalCaller request), finalTrace trace request⟩)
    simp [ReusableResponse.step, ReusableResponseSource.step, Reification.timedStep,
      Reification.terminal, finalCaller, PMF.pure_map]) horizon (by rw [budget]; exact hBudget)
  rw [semantics, PMF.pure_map] at h
  exact h

end Foundation.Examples.ReusableResponseTwoQueries
