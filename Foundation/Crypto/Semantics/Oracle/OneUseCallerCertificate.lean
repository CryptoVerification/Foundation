import Foundation.Crypto.Semantics.Oracle.OneUseCallerDistribution

/-! A caller-level stopping certificate is sufficient to construct the
whole native consumer. Logical bounds are kept separate from physical costs;
the final distribution equality is included for observed game adapters. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

structure CallerCertificate (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool)) (callerFrame : Configuration State) where
  fuel : Nat
  positive : 0 < fuel
  predicate : Boundary State → Prop
  closed : ∀ source, predicate source →
    ∀ result ∈ ((automaticRound stateSize code oracle key keyTail fuel).semantics source).support, predicate result
  extentCap : Nat
  extentBound : ∀ source, predicate source → ControllerExtent.sourceExtent stateSize
    (embed (Machine.PairPreparation.operand [] key keyTail) source) ≤ extentCap
  logicalBound : Nat
  count : Nat
  countBound : logicalBound ≤ count
  initial : predicate ⟨false, callerFrame⟩
  stops : ∀ final ∈ (TimedExecution.eval (callerStep code oracle key keyTail) logicalBound ⟨false, callerFrame⟩).support,
    Reification.terminal final.frame.control = true

namespace CallerCertificate
variable {stateSize : State → Nat} {code : Code} {oracle : BitOracle State}
    {key : List Bool} {keyTail : List (Option Bool)} {callerFrame : Configuration State}
    (C : CallerCertificate stateSize code oracle key keyTail callerFrame)

noncomputable def automatic : AutomaticCertificate stateSize code oracle key keyTail callerFrame :=
  AutomaticCertificate.ofCallerStop stateSize code oracle key keyTail callerFrame C.fuel C.positive
    C.predicate C.closed C.initial C.logicalBound C.count C.countBound C.stops C.extentCap C.extentBound

def physicalBudget : Nat := C.count * (C.fuel + (33 * (key.length + C.extentCap + C.fuel * 2) + 33))

noncomputable def consumer := C.automatic.consumer

theorem consumer_budget : C.consumer.execution.budget () = C.physicalBudget :=
  C.automatic.consumer_budget

theorem consumer_semantics : C.consumer.execution.semantics () =
    (TimedExecution.eval (callerStep code oracle key keyTail) C.logicalBound ⟨false, callerFrame⟩).map
      (embed (Machine.PairPreparation.operand [] key keyTail)) := by
  rw [consumer, AutomaticCertificate.consumer_semantics]
  change (TimedExecution.eval (automaticRound stateSize code oracle key keyTail C.fuel).semantics
    C.count ⟨false, callerFrame⟩).map _ = _
  rw [← caller_distribution code oracle key keyTail stateSize C.fuel C.positive
    ⟨false, callerFrame⟩ C.logicalBound C.count C.countBound C.stops]

end CallerCertificate
end CryptoOracle.Interactive.OneUseSourceRounds
