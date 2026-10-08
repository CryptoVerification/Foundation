import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableResponse
import Foundation.Crypto.Semantics.Oracle.ReusableResponseStorage

/-! Whole retained-data resources for arbitrarily many response requests.
The extent of the actual key/payload objects is not doubled at each call. -/
namespace Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Resources
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open PrivacyStorage (responderCells responderExtent)
universe u
set_option backward.isDefEq.respectTransparency false

theorem responder_extent_step (program : Program) (start target : ResponseHandoff.Control)
    (h : target ∈ (ResponseHandoffProgram.step program start).support) :
    responderExtent target ≤ responderExtent start + 1 := by
  cases start with
  | headerWriting key remaining buffer =>
      cases remaining <;> simp [ResponseHandoffProgram.step, ResponseHandoff.step] at h <;> subst target <;>
        simp only [responderExtent, Machine.ControllerExtent.machine, Tape.cells_write,
          List.length_cons] <;> omega
  | headerAdvancing key remaining buffer =>
      have hb := Tape.cells_moveRight_le buffer
      simp [ResponseHandoffProgram.step, ResponseHandoff.step] at h
      subst target
      simp only [responderExtent]
      omega
  | copying machine =>
      by_cases hh : machine.halted = true
      · simp [ResponseHandoffProgram.step, ResponseHandoff.step, hh] at h
        subst target
        exact le_add_right (Nat.le_refl _)
      · simp only [ResponseHandoffProgram.step, ResponseHandoff.step, hh, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_map_iff] at h
        obtain ⟨native, hn, he⟩ := h
        subst target
        exact Machine.ControllerExtent.native_bound PrivateKeyCopy.code machine native hn
  | rewinding key buffer =>
      have hb := Tape.cells_moveLeft_le buffer
      cases hl : buffer.left <;> simp [ResponseHandoffProgram.step, ResponseHandoff.step, hl] at h <;> subst target <;>
        simp only [responderExtent, Machine.ControllerExtent.machine]
      · change max key.cells (max buffer.cells 1) ≤ max key.cells buffer.cells + 1
        omega
      · omega
  | authenticating key machine =>
      simp only [ResponseHandoffProgram.step, ResponseHandoff.step, PMF.mem_support_map_iff] at h
      obtain ⟨native, hn, he⟩ := h
      subst target
      have hb := Machine.ControllerExtent.native_bound program machine native hn
      simp only [responderExtent]
      omega

theorem ready_extent (component : ResponseHandoff.Control) (machine : Machine.Configuration) (key : Tape)
    (h : ResponseHandoffProgram.Callback.ready component = some (machine, key)) :
    Machine.ControllerExtent.machine machine ≤ responderExtent component ∧ key.cells ≤ responderExtent component := by
  cases component <;> simp only [ResponseHandoffProgram.Callback.ready, reduceCtorEq] at h
  split at h
  · cases h
    simp only [responderExtent]
    omega
  · contradiction

theorem begin_extent (key : Tape) (request : List Bool) :
    responderExtent (ReusableResponse.begin key request) ≤ max key.cells request.length + 1 := by
  simp only [ReusableResponse.begin, responderExtent, Tape.cells, List.length_nil]
  omega

variable {State : Type u} (stateSize : State → Nat)
abbrev cells := ReusableResponseStorage.cells responderCells stateSize Tape.cells
abbrev extent := ReusableResponseStorage.extent responderExtent stateSize Tape.cells

theorem cells_bound (c : ReusableResponse.Control State) :
    cells stateSize c ≤ 4 * (extent stateSize c) ^ 2 + 13 * extent stateSize c + 1 :=
  ReusableResponseStorage.cells_bound responderCells responderExtent stateSize Tape.cells 3 0
    PrivacyStorage.responder_cells c

variable (program : Program) (code : Code) (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hOracle in
theorem extent_step (start target : ReusableResponse.Control State)
    (h : target ∈ (ReusableResponse.step program code oracle start).support) :
    extent stateSize target ≤ extent stateSize start + (stateIncrement + responseCap + 4) := by
  have hb := ReusableResponseStorage.extent_step responderExtent stateSize Tape.cells
    (ResponseHandoffProgram.step program) ReusableResponse.begin ResponseHandoffProgram.Callback.ready program code oracle
    1 1 stateIncrement responseCap begin_extent (responder_extent_step program) ready_extent hOracle start target h
  change extent stateSize target ≤ extent stateSize start + (1 + 1 + stateIncrement + responseCap + 2) at hb
  omega

include hOracle in
theorem peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start target : ReusableResponse.Control State)
    (hTarget : target ∈ (TimedExecution.eval (ReusableResponse.step program code oracle) elapsed start).support) :
    cells stateSize target ≤ ReusableResponseStorage.bound (extent stateSize start) horizon 1 1 stateIncrement responseCap 3 0 :=
  ReusableResponseStorage.peak responderCells responderExtent stateSize Tape.cells 3 0 PrivacyStorage.responder_cells
    (ResponseHandoffProgram.step program) ReusableResponse.begin ResponseHandoffProgram.Callback.ready program code oracle
    1 1 stateIncrement responseCap begin_extent (responder_extent_step program) ready_extent hOracle
    horizon elapsed hElapsed start target hTarget

theorem bound_polynomial {initialExtent horizon stateIncrement responseCap : Nat → Nat}
    (hExtent : PolynomiallyBounded initialExtent) (hTime : PolynomiallyBounded horizon)
    (hIncrement : PolynomiallyBounded stateIncrement) (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => ReusableResponseStorage.bound (initialExtent n) (horizon n) 1 1
      (stateIncrement n) (responseCap n) 3 0) :=
  ReusableResponseStorage.bound_polynomial hExtent hTime (PolynomiallyBounded.const 1)
    (PolynomiallyBounded.const 1) hIncrement hResponse 3 0

end Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Resources
