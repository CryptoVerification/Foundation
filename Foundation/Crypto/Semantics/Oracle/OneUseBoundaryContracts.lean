import Foundation.Crypto.Semantics.Oracle.OneUseSourceInterval
import Foundation.Crypto.Semantics.ProcedureInvariant

/-! Certify that actual query returns and ordinary caller intervals retain
one fixed private-key layout at a source boundary. The certificate includes
the complete caller frame, use flag and actual time; it does not expose a
proof coordinate as an instruction or perform a free memory copy. -/
namespace CryptoOracle.Interactive.OneUseBoundaryContracts
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def stored (key : Machine.Tape) (control : OneUseSource.Control State) : Prop :=
  ∃ spent frame, control = .source spent key frame

variable (code : Code) (oracle : BitOracle State) (machine : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool))
    (key request : List Bool) (keyTail requestTail : List (Option Bool))
    (hActive : machine.halted = false) (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape [] requestTail request)

noncomputable def query (spent : Bool) :=
  (OneUseXorRequest.invocation code oracle machine state trace key request keyTail requestTail
    hActive hCall hTape spent).certify (stored (Machine.PairPreparation.operand [] key keyTail))
    (by
      intro _ output hs
      rw [OneUseXorRequest.semantics, PMF.mem_support_pure_iff] at hs
      subst output
      exact ⟨OneUseXorRequest.used spent key request, _, rfl⟩)

/-- Removing only proof data recovers the full physical state/time law. -/
theorem query_costed (spent : Bool) :
    ((query code oracle machine state trace key request keyTail requestTail hActive hCall hTape spent).costed ()).map
      (fun result => (result.1.val, result.2)) =
      (OneUseXorRequest.invocation code oracle machine state trace key request keyTail requestTail
        hActive hCall hTape spent).costed () :=
  Procedure.certify_costed _ _ _ ()

theorem query_semantics (spent : Bool) :
    ((query code oracle machine state trace key request keyTail requestTail hActive hCall hTape spent).semantics ()).map
      Subtype.val = PMF.pure (OneUseXorRequest.result machine state trace key request keyTail spent) := by
  rw [query, Procedure.certify_semantics, OneUseXorRequest.semantics]

variable (native : Machine.Program) (store : Machine.Tape)

noncomputable def caller (spent : Bool) (fuel : Nat) :=
  (OneUseSourceInterval.interval native code oracle spent store fuel).physical.certify (stored store)
    (by
      intro initial output hs
      change output ∈ (((OneUseSourceInterval.interval native code oracle spent store fuel).semantics initial).map
        (OneUseSourceInterval.embed spent store)).support at hs
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨frame, _, he⟩ := hs
      subst output
      exact ⟨spent, frame, rfl⟩)

/-- The private store certificate covers random ordinary instructions as
well as deterministic ones and preserves their actual duration distribution. -/
theorem caller_costed (spent : Bool) (fuel : Nat) (frame : Configuration State) :
    ((caller code oracle native store spent fuel).costed frame).map
      (fun result => (result.1.val, result.2)) =
      ((OneUseSourceInterval.interval native code oracle spent store fuel).physical).costed frame :=
  Procedure.certify_costed _ _ _ frame

end CryptoOracle.Interactive.OneUseBoundaryContracts
