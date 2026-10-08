import Foundation.Crypto.Semantics.Oracle.AdaptiveBitstringLoopExecution
import Foundation.Crypto.Semantics.Oracle.StructuredCodeStorage

/-! Whole-prefix encoded memory for the arbitrary-bitstring adaptive caller.
The measure includes the actual source tapes, exported request, response
loading buffers, complete transcript and a supplied codec for oracle state.
Oracle-state growth is an explicit experiment-side premise. -/
namespace CryptoOracle.Interactive.AdaptiveBitstringLoop
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

variable {State : Type u}

theorem initial_extent (stateSize : State → Nat) (state : State) (rounds : Nat) (request : List Bool) :
    ControllerExtent.frameExtent stateSize (frame state rounds [] request []) ≤
      stateSize state + rounds + request.length + 2 := by
  cases rounds <;> cases request <;>
    simp [frame, machine, ControllerExtent.frameExtent, ControllerExtent.controlExtent, ControllerExtent.traceExtent,
      Machine.ControllerExtent.machine, ResponseLoading.loaded, ResponseLoading.fromCells, Tape.ofBits, Tape.cells,
      List.replicate_succ]
  all_goals omega

def bitBound (initialStateSize stateIncrement cap rounds requestSize : Nat) : Nat :=
  StructuredCodeStorage.bound code 0 (initialStateSize + rounds + requestSize + 2)
    (timeBound cap rounds requestSize) stateIncrement cap

theorem storage_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (stateIncrement cap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ cap)
    (state : State) (rounds : Nat) (request : List Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ timeBound cap rounds request.length) (target : Configuration State)
    (h : target ∈ (TimedExecution.eval (Reification.timedStep code oracle) elapsed
      (frame state rounds [] request [])).support) :
    ((StructuredCodeStorage.completeEncoding E).encode (code, target)).length ≤
      bitBound (stateSize state) stateIncrement cap rounds request.length := by
  have hp := StructuredCodeStorage.peak E stateSize hState code oracle stateIncrement cap hOracle
    (timeBound cap rounds request.length) elapsed hElapsed (frame state rounds [] request []) target h
  change _ ≤ StructuredCodeStorage.bound code 0 _ _ _ _ at hp
  exact hp.trans (StructuredCodeStorage.bound_mono code (Nat.le_refl _) (initial_extent stateSize state rounds request)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

theorem space_polynomial {initialStateSize stateIncrement cap rounds requestSize : Nat → Nat}
    (hState : PolynomiallyBounded initialStateSize) (hIncrement : PolynomiallyBounded stateIncrement)
    (hCap : PolynomiallyBounded cap) (hRounds : PolynomiallyBounded rounds) (hRequest : PolynomiallyBounded requestSize) :
    PolynomiallyBounded (fun n => bitBound (initialStateSize n) (stateIncrement n) (cap n) (rounds n) (requestSize n)) :=
  StructuredCodeStorage.bound_polynomial code (PolynomiallyBounded.const 0)
    (((hState.add hRounds).add hRequest).add (PolynomiallyBounded.const 2))
    (time_polynomial hCap hRounds hRequest) hIncrement hCap

end CryptoOracle.Interactive.AdaptiveBitstringLoop
