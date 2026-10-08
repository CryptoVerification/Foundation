import Foundation.Crypto.Semantics.IterationTermination
import Foundation.Crypto.Semantics.Oracle.OneUseAutomaticCertificate
import Foundation.Crypto.Semantics.Oracle.OneUseProgramContract

/-! A whole-machine stopping proof can supply the stopping field of a
one-use round certificate. Actual reachability and positive progress are
explicit obligations, restricted to the proved admissibility invariant. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool)) (callerFrame : Configuration State)
    (fuel : Nat) (predicate : Boundary State → Prop)
    (hClosed : ∀ source, predicate source →
      ∀ result ∈ ((automaticRound stateSize code oracle key keyTail fuel).semantics source).support, predicate result)
    (hOperational : ∀ source, predicate source →
      ∀ result ∈ ((automaticRound stateSize code oracle key keyTail fuel).costed source).support,
        embed (Machine.PairPreparation.operand [] key keyTail) result.1 ∈
          (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
            result.2 (embed (Machine.PairPreparation.operand [] key keyTail) source)).support)
    (hProgress : ∀ source, predicate source → Reification.terminal source.frame.control = false →
      ∀ result ∈ ((automaticRound stateSize code oracle key keyTail fuel).costed source).support, 0 < result.2)
    (hInitial : predicate ⟨false, callerFrame⟩) (bound count : Nat) (hCount : bound ≤ count)
    (hStop : ∀ physical ∈ (TimedExecution.eval
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) bound
      (embed (Machine.PairPreparation.operand [] key keyTail) ⟨false, callerFrame⟩)).support,
        OneUseProgramContract.terminal physical = true)

include hClosed hOperational hProgress hInitial hCount hStop in
theorem automatic_stops_of_machine (final : Boundary State)
    (hFinal : final ∈ (TimedExecution.eval
      (automaticRound stateSize code oracle key keyTail fuel).semantics count ⟨false, callerFrame⟩).support) :
    Reification.terminal final.frame.control = true :=
  Procedure.invariant_stops_of_machine
    (automaticRound stateSize code oracle key keyTail fuel) predicate hClosed hOperational
    (fun _ _ _ _ => rfl) OneUseProgramContract.terminal
    (OneUseProgramContract.absorbing Machine.OneTimePad.Prepared.listProcedure.code code oracle)
    hProgress ⟨⟨false, callerFrame⟩, hInitial⟩ bound count hCount hStop final hFinal

/-- Derive the stopping field from genuine whole-machine execution, instead
of assuming that every result of the logical round iteration is terminal. -/
noncomputable def AutomaticCertificate.ofMachineStop (extentCap : Nat)
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
  stops := automatic_stops_of_machine stateSize code oracle key keyTail callerFrame fuel predicate hClosed
    hOperational hProgress hInitial bound count hCount hStop

end CryptoOracle.Interactive.OneUseSourceRounds
