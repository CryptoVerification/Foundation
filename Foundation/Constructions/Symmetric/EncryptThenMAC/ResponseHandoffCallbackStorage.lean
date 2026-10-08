import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoffCallback
import Foundation.Crypto.Semantics.Oracle.ComponentResponseStorage

/-! Complete retained-data resources for response preparation, ownership
transfer, delivery and continued caller execution. The fixed environment and
its active source copy are counted separately. -/
namespace Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.Callback.Storage
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

variable {State : Type u} (stateSize : State → Nat)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

abbrev cells := ComponentResponseStorage.cells PrivacyStorage.responderCells stateSize Tape.cells caller state trace request
abbrev extent := ComponentResponseStorage.extent PrivacyStorage.responderCells stateSize Tape.cells caller state trace request

/-- The handoff retains the existing native machine and key, whose sizes
are already included in the responder's complete cell count. -/
theorem ready_resources (component : ResponseHandoff.Control) (machine : Machine.Configuration) (key : Tape)
    (h : Callback.ready component = some (machine, key)) :
    Machine.ControllerExtent.machine machine ≤ PrivacyStorage.responderCells component ∧
      key.cells ≤ PrivacyStorage.responderCells component := by
  cases component <;> simp only [Callback.ready, reduceCtorEq] at h
  rename_i retained native
  split at h
  · cases h
    simp only [PrivacyStorage.responderCells, Machine.ControllerExtent.machine, Machine.Configuration.tapeCells]
    omega
  · contradiction

theorem cells_bound (c : ComponentResponseCallback.Control ResponseHandoff.Control State Tape) :
    cells stateSize caller state trace request c ≤
      4 * (extent stateSize caller state trace request c) ^ 2 +
        11 * extent stateSize caller state trace request c + 1 :=
  ComponentResponseStorage.cells_bound PrivacyStorage.responderCells PrivacyStorage.responderCells
    stateSize Tape.cells caller state trace request 1 0 (fun _ => by omega) c

variable (program : Program) (code : Code) (oracle : BitOracle State)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hOracle in
theorem extent_step (start target : ComponentResponseCallback.Control ResponseHandoff.Control State Tape)
    (h : target ∈ (Callback.step program code oracle caller state trace request start).support) :
    extent stateSize caller state trace request target ≤ extent stateSize caller state trace request start +
      (stateIncrement + responseCap + 3) := by
  have hb := ComponentResponseStorage.extent_step PrivacyStorage.responderCells stateSize Tape.cells caller state trace request
    (ResponseHandoffProgram.step program) Callback.ready program code oracle 1 stateIncrement responseCap
    (ResponseHandoffProgram.cells_step program) ready_resources hOracle start target h
  change extent stateSize caller state trace request target ≤ extent stateSize caller state trace request start + (1 + stateIncrement + responseCap + 2) at hb
  omega

include hOracle in
theorem peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : ComponentResponseCallback.Control ResponseHandoff.Control State Tape)
    (hTarget : target ∈ (TimedExecution.eval (Callback.step program code oracle caller state trace request) elapsed start).support) :
    cells stateSize caller state trace request target ≤
      ComponentResponseStorage.bound (extent stateSize caller state trace request start)
        horizon 1 stateIncrement responseCap 1 0 :=
  ComponentResponseStorage.peak PrivacyStorage.responderCells PrivacyStorage.responderCells
    stateSize Tape.cells caller state trace request 1 0 (fun _ => by omega)
    (ResponseHandoffProgram.step program) Callback.ready program code oracle 1 stateIncrement responseCap
    (ResponseHandoffProgram.cells_step program) ready_resources hOracle horizon elapsed hElapsed start target hTarget

theorem bound_polynomial {initialExtent horizon stateIncrement responseCap : Nat → Nat}
    (hExtent : PolynomiallyBounded initialExtent) (hTime : PolynomiallyBounded horizon)
    (hIncrement : PolynomiallyBounded stateIncrement) (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => ComponentResponseStorage.bound (initialExtent n) (horizon n)
      1 (stateIncrement n) (responseCap n) 1 0) :=
  ComponentResponseStorage.bound_polynomial hExtent hTime (PolynomiallyBounded.const 1) hIncrement hResponse 1 0

end Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.Callback.Storage
