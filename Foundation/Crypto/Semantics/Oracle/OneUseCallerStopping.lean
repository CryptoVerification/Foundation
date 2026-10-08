import Foundation.Crypto.Semantics.Oracle.OneUseCallerSemantics
import Foundation.Crypto.Semantics.Oracle.OneUseAutomaticCertificate
import Foundation.Crypto.Semantics.IterationTermination

/-! Caller-level query counting supplies a real whole-program contract:
logical stopping is proved on the same finite caller and transported through
the ordinary/query round. Physical query costs remain in the native contract.
No separate whole-physical-machine stopping proof is requested. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool))

theorem automatic_stops_of_caller (fuel : Nat) (hFuel : 0 < fuel) (start : Boundary State)
    (bound count : Nat) (hCount : bound ≤ count)
    (hStop : ∀ final ∈ (TimedExecution.eval (callerStep code oracle key keyTail) bound start).support,
      Reification.terminal final.frame.control = true)
    (final : Boundary State)
    (hFinal : final ∈ (TimedExecution.eval
      (automaticRound stateSize code oracle key keyTail fuel).semantics count start).support) :
    Reification.terminal final.frame.control = true := by
  have hMarginal : (fun source => (callerRound code oracle key keyTail fuel source).map Prod.fst) =
      (automaticRound stateSize code oracle key keyTail fuel).semantics :=
    funext (callerRound_marginal code oracle key keyTail stateSize fuel)
  apply CostedIteration.terminal_of_steps (callerStep code oracle key keyTail)
    (fun source => Reification.terminal source.frame.control)
    (callerStep_terminal code oracle key keyTail)
    (callerRound code oracle key keyTail fuel) id (callerRound_reachable code oracle key keyTail fuel)
    (fun source _ => callerRound_positive code oracle key keyTail fuel hFuel source)
    start bound count hCount hStop final
  rwa [hMarginal]

variable (callerFrame : Configuration State) (fuel : Nat) (hFuel : 0 < fuel)
    (predicate : Boundary State → Prop)
    (hClosed : ∀ source, predicate source →
      ∀ result ∈ ((automaticRound stateSize code oracle key keyTail fuel).semantics source).support, predicate result)
    (hInitial : predicate ⟨false, callerFrame⟩) (bound count : Nat) (hCount : bound ≤ count)
    (hStop : ∀ final ∈ (TimedExecution.eval (callerStep code oracle key keyTail) bound ⟨false, callerFrame⟩).support,
      Reification.terminal final.frame.control = true)

/-- Logical caller stopping and an admissible extent cap supply the native
resource certificate, including real query processing and final caller halt. -/
noncomputable def AutomaticCertificate.ofCallerStop (extentCap : Nat)
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
  stops := automatic_stops_of_caller stateSize code oracle key keyTail fuel hFuel
    ⟨false, callerFrame⟩ bound count hCount hStop

end CryptoOracle.Interactive.OneUseSourceRounds
