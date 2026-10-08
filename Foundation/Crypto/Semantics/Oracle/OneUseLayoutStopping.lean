import Foundation.Crypto.Semantics.Oracle.OneUseOperational
import Foundation.Crypto.Semantics.Oracle.OneUseProgress
import Foundation.Crypto.Semantics.Oracle.OneUseMachineStopping

/-! A real layout at every admissible nonterminal call boundary discharges
the operational reachability and progress obligations of the machine-stop
bridge. Normal requests, invalid lengths and spent rejections all qualify. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool)) (callerFrame : Configuration State)
    (fuel : Nat) (hFuel : 0 < fuel) (predicate : Boundary State → Prop)
    (hClosed : ∀ source, predicate source →
      ∀ result ∈ ((automaticRound stateSize code oracle key keyTail fuel).semantics source).support, predicate result)
    (hLayout : ∀ source, predicate source → Reification.terminal source.frame.control = false →
      OneUseSourceInterval.boundary code source.frame.control = true → Nonempty (CallLayout code source.frame))
    (hInitial : predicate ⟨false, callerFrame⟩) (bound count : Nat) (hCount : bound ≤ count)
    (hStop : ∀ physical ∈ (TimedExecution.eval
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) bound
      (embed (Machine.PairPreparation.operand [] key keyTail) ⟨false, callerFrame⟩)).support,
        OneUseProgramContract.terminal physical = true)

include hFuel hClosed hLayout hInitial hCount hStop in
theorem automatic_stops_of_layout (final : Boundary State)
    (hFinal : final ∈ (TimedExecution.eval
      (automaticRound stateSize code oracle key keyTail fuel).semantics count ⟨false, callerFrame⟩).support) :
    Reification.terminal final.frame.control = true :=
  automatic_stops_of_machine stateSize code oracle key keyTail callerFrame fuel predicate hClosed
    (fun source _ => automaticRound_operational code oracle key keyTail stateSize fuel source)
    (fun source hs ht => round_progress code oracle key keyTail fuel hFuel _ _ source
      (hLayout source hs ht)) hInitial bound count hCount hStop final hFinal

/-- No independent actual-reachability or positive-cost proof is requested
from the client. Both follow from the physical query layout and real code. -/
noncomputable def AutomaticCertificate.ofLayoutStop (extentCap : Nat)
    (hExtent : ∀ source, predicate source → ControllerExtent.sourceExtent stateSize
      (embed (Machine.PairPreparation.operand [] key keyTail) source) ≤ extentCap) :
    AutomaticCertificate stateSize code oracle key keyTail callerFrame where
  fuel := fuel
  predicate := predicate
  closed := hClosed
  extentCap := extentCap
  extentBound := hExtent
  count := count
  initial := hInitial
  stops := automatic_stops_of_layout stateSize code oracle key keyTail callerFrame fuel hFuel predicate hClosed
    hLayout hInitial bound count hCount hStop

end CryptoOracle.Interactive.OneUseSourceRounds

namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {code : Code} {oracle : BitOracle State}
    {key : List Bool} {keyTail : List (Option Bool)} {callerFrame : Configuration State}

/-- Reachability at accumulated actual cost survives the complete certified
caller, including restriction, iteration, fixed entry and physical output. -/
theorem Certificate.consumer_operational (C : Certificate code oracle key keyTail callerFrame) :
    Procedure.Operational C.consumer.execution := by
  change Procedure.Operational C.procedure.physical
  apply Procedure.operational_physical
  unfold Certificate.procedure
  apply Procedure.operational_reindex
  unfold execution
  apply Procedure.operational_invariantIteration
  intro source _ result hs
  exact round_operational code oracle key keyTail C.fuel C.cap C.capProof source result hs

theorem AutomaticCertificate.consumer_operational {stateSize : State → Nat}
    (C : AutomaticCertificate stateSize code oracle key keyTail callerFrame) :
    Procedure.Operational C.consumer.execution := C.certificate.consumer_operational

end CryptoOracle.Interactive.OneUseSourceRounds
