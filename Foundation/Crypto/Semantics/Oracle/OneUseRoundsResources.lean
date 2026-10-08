import Foundation.Crypto.Semantics.Oracle.OneUseSourceRounds
import Foundation.Crypto.Semantics.Asymptotic.PolynomiallyBounded

/-! Whole-round retained-data profiles count the initial caller, private
store, and all intermediate controller copies. Polynomial resource claims
require polynomial initial data and polynomial step-growth profiles. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def memoryBudget (initialExtent count bound increment : Nat) : Nat :=
  4 * (initialExtent + count * bound * increment) ^ 2 +
    11 * (initialExtent + count * bound * increment) + 2

theorem memory_peak (code : Code) (oracle : BitOracle State) (key : List Bool) (keyTail : List (Option Bool))
    (stateSize : State → Nat) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request answer, answer ∈ (oracle state request).support →
      stateSize answer.1 ≤ stateSize state + stateIncrement ∧ answer.2.length ≤ responseCap)
    (count bound elapsed : Nat) (hElapsed : elapsed ≤ count * bound) (source : Boundary State)
    (target : OneUseSource.Control State)
    (h : target ∈ (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      elapsed (embed (Machine.PairPreparation.operand [] key keyTail) source)).support) :
    ControllerStorage.sourceCells stateSize target ≤
      memoryBudget (ControllerExtent.sourceExtent stateSize
        (embed (Machine.PairPreparation.operand [] key keyTail) source)) count bound (stateIncrement + responseCap + 2) := by
  have hExtent := ResourceGrowth.prefix_bound
    (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
    (ControllerExtent.sourceExtent stateSize) (stateIncrement + responseCap + 2)
    (ControllerExtent.source_step stateSize Machine.OneTimePad.Prepared.listProcedure.code code oracle
      stateIncrement responseCap hOracle) (count * bound) elapsed hElapsed
    (embed (Machine.PairPreparation.operand [] key keyTail) source) target h
  have hCells := ControllerExtent.source_cells stateSize target
  have hPow := Nat.pow_le_pow_left hExtent 2
  unfold memoryBudget
  omega

/-- Request-size certificates suffice to derive the query cap for every
actual ordinary-interval return, including invalid lengths and spent keys. -/
noncomputable def boundedRound (code : Code) (oracle : BitOracle State) (key : List Bool)
    (keyTail : List (Option Bool)) (fuel : Nat) (requestCap : Boundary State → Nat)
    (hRequest : ∀ source result, result ∈ ((caller code oracle key keyTail fuel).semantics source).support →
      ∀ data : CallLayout code result.frame, data.request.length ≤ requestCap source) :=
  round code oracle key keyTail fuel (fun source => 33 * (key.length + requestCap source) + 33)
    (fun source result hs => queryAt_budget_bound code oracle key keyTail result (requestCap source)
      (hRequest source result hs))

theorem round_profile_polynomial {fuel keyLength requestCap : Nat → Nat}
    (hFuel : PolynomiallyBounded fuel) (hKey : PolynomiallyBounded keyLength)
    (hRequest : PolynomiallyBounded requestCap) :
    PolynomiallyBounded (fun n => fuel n + (33 * (keyLength n + requestCap n) + 33)) :=
  hFuel.add (((PolynomiallyBounded.const 33).mul (hKey.add hRequest)).add (PolynomiallyBounded.const 33))

theorem time_profile_polynomial {count bound : Nat → Nat}
    (hCount : PolynomiallyBounded count) (hBound : PolynomiallyBounded bound) :
    PolynomiallyBounded (fun n => count n * bound n) := hCount.mul hBound

/-- Existing data and retained growth must be bounded explicitly. A
logical stopping certificate alone supplies neither of those bounds. -/
theorem memory_profile_polynomial {initialExtent count bound increment : Nat → Nat}
    (hInitial : PolynomiallyBounded initialExtent) (hCount : PolynomiallyBounded count)
    (hBound : PolynomiallyBounded bound) (hIncrement : PolynomiallyBounded increment) :
    PolynomiallyBounded (fun n => memoryBudget (initialExtent n) (count n) (bound n) (increment n)) := by
  have he := hInitial.add ((hCount.mul hBound).mul hIncrement)
  have hb := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 11).mul he)).add (PolynomiallyBounded.const 2)
  simpa only [memoryBudget, pow_two] using hb

end CryptoOracle.Interactive.OneUseSourceRounds
