import Foundation.Crypto.Semantics.Oracle.OneUseAutomaticBounds
import Foundation.Crypto.Semantics.Oracle.OneUseRoundCertificate

/-! A finite-round certificate whose request and query caps are derived from
physical extent. Clients prove closure, an admissible extent cap, and real
stopping; they do not separately assume a request-size or query-time cap. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

structure AutomaticCertificate (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool)) (callerFrame : Configuration State) where
  fuel : Nat
  predicate : Boundary State → Prop
  closed : ∀ source, predicate source →
    ∀ result ∈ ((automaticRound stateSize code oracle key keyTail fuel).semantics source).support, predicate result
  extentCap : Nat
  extentBound : ∀ source, predicate source → ControllerExtent.sourceExtent stateSize
    (embed (Machine.PairPreparation.operand [] key keyTail) source) ≤ extentCap
  count : Nat
  initial : predicate ⟨false, callerFrame⟩
  stops : ∀ final ∈ (TimedExecution.eval (automaticRound stateSize code oracle key keyTail fuel).semantics
    count ⟨false, callerFrame⟩).support, Reification.terminal final.frame.control = true

namespace AutomaticCertificate
variable {stateSize : State → Nat} {code : Code} {oracle : BitOracle State}
    {key : List Bool} {keyTail : List (Option Bool)} {callerFrame : Configuration State}
    (C : AutomaticCertificate stateSize code oracle key keyTail callerFrame)

noncomputable def certificate : Certificate code oracle key keyTail callerFrame where
  fuel := C.fuel
  cap := fun source => 33 * (key.length + requestCap stateSize key keyTail C.fuel source) + 33
  capProof := fun source result hs => queryAt_budget_bound code oracle key keyTail result
    (requestCap stateSize key keyTail C.fuel source)
    (request_bound stateSize code oracle key keyTail C.fuel source result hs)
  predicate := C.predicate
  closed := C.closed
  bound := C.fuel + (33 * (key.length + C.extentCap + C.fuel * 2) + 33)
  bounded := by
    intro source hSource
    have he := C.extentBound source hSource
    simp only [requestCap]
    omega
  count := C.count
  initial := C.initial
  stops := C.stops

noncomputable def consumer := C.certificate.consumer

theorem consumer_budget : C.consumer.execution.budget () =
    C.count * (C.fuel + (33 * (key.length + C.extentCap + C.fuel * 2) + 33)) :=
  C.certificate.consumer_budget

theorem consumer_semantics : C.consumer.execution.semantics () =
    (TimedExecution.eval (automaticRound stateSize code oracle key keyTail C.fuel).semantics C.count
      (Boundary.mk false callerFrame)).map (embed (Machine.PairPreparation.operand [] key keyTail)) :=
  C.certificate.consumer_semantics

end AutomaticCertificate

/-- Uniform physical extent and ordinary fuel produce a polynomial round
cap; multiplication by a polynomial round count bounds whole execution. -/
theorem automatic_profile_polynomial {fuel keyLength extentCap count : Nat → Nat}
    (hFuel : PolynomiallyBounded fuel) (hKey : PolynomiallyBounded keyLength)
    (hExtent : PolynomiallyBounded extentCap) (hCount : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n => count n *
      (fuel n + (33 * (keyLength n + extentCap n + fuel n * 2) + 33))) :=
  hCount.mul (hFuel.add (((PolynomiallyBounded.const 33).mul
    ((hKey.add hExtent).add (hFuel.mul (PolynomiallyBounded.const 2)))).add (PolynomiallyBounded.const 33)))

end CryptoOracle.Interactive.OneUseSourceRounds
