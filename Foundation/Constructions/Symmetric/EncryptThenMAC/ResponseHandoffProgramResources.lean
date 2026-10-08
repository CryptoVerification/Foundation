import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoffProgram
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyEncoding
import Foundation.Crypto.Semantics.Oracle.PrivateEncodedStorage

/-! Whole-code/state resources for arbitrary-payload response handling.
Transient copies, retained private key and native addresses are included. -/
namespace Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram
open Machine Foundation.Probability CryptoOracle.Interactive
set_option backward.isDefEq.respectTransparency false
open PrivacyEncoding (responderPc)

theorem pc_step (program : Program) (start target : ResponseHandoff.Control)
    (h : target ∈ (step program start).support) :
    responderPc target ≤ responderPc start + (PrivateKeyCopy.code.addressCap + program.addressCap + 1) := by
  cases start with
  | headerWriting key rest buffer =>
      cases rest <;> simp [step, ResponseHandoff.step] at h <;> subst target <;> simp [responderPc]
  | headerAdvancing key rest buffer =>
      simp [step, ResponseHandoff.step] at h
      subst target
      simp [responderPc]
  | copying c =>
      by_cases hh : c.halted = true
      · simp [step, ResponseHandoff.step, hh] at h
        subst target
        simp [responderPc]
      · simp only [step, ResponseHandoff.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨next, hn, he⟩ := h
        subst target
        have hp := Machine.pc_le_of_support _ c next hn
        simp only [responderPc]
        omega
  | rewinding key buffer =>
      cases ht : buffer.left <;> simp [step, ResponseHandoff.step, ht] at h <;> subst target <;> simp [responderPc]
  | authenticating key c =>
      simp only [step, ResponseHandoff.step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, he⟩ := h
      subst target
      have hp := Machine.pc_le_of_support _ c next hn
      simp only [responderPc]
      omega

theorem cells_step (program : Program) (start target : ResponseHandoff.Control)
    (h : target ∈ (step program start).support) :
    PrivacyStorage.responderCells target ≤ PrivacyStorage.responderCells start + 1 := by
  cases start with
  | headerWriting key rest buffer =>
      cases rest <;> simp [step, ResponseHandoff.step] at h <;> subst target <;>
        simp only [PrivacyStorage.responderCells, Configuration.tapeCells, Tape.cells_write, List.length_cons] <;> omega
  | headerAdvancing key rest buffer =>
      have hm := Tape.cells_moveRight_le buffer
      simp [step, ResponseHandoff.step] at h
      subst target
      simp only [PrivacyStorage.responderCells]
      omega
  | copying c =>
      by_cases hh : c.halted = true
      · simp [step, ResponseHandoff.step, hh] at h
        subst target
        simp [PrivacyStorage.responderCells, Configuration.tapeCells]
      · simp only [step, ResponseHandoff.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨next, hn, he⟩ := h
        subst target
        exact Machine.tapeCells_le_of_support _ c next hn
  | rewinding key buffer =>
      have hm := Tape.cells_moveLeft_le buffer
      cases ht : buffer.left <;> simp [step, ResponseHandoff.step, ht] at h <;> subst target <;>
        simp only [PrivacyStorage.responderCells, Configuration.tapeCells, Tape.cells, List.length_nil] at * <;> omega
  | authenticating key c =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, he⟩ := h
      subst target
      have hm := Machine.tapeCells_le_of_support _ c next hn
      simp only [PrivacyStorage.responderCells]
      omega

def completeEncoding := PrivateControllerEncoding.programEncoding.prod
  (PrivateControllerEncoding.programEncoding.prod PrivacyEncoding.responder)

private theorem complete_length (first second : Program) (c : ResponseHandoff.Control) :
    (completeEncoding.encode (first, second, c)).length =
      (2 * (Program.encode first).length + 2 * (Program.encode second).length + 2) +
        (PrivacyEncoding.responder.encode c).length := by
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length, PrivateControllerEncoding.programEncoding]
  omega

def bound (program : Program) (initialPc initialCells horizon : Nat) : Nat :=
  (2 * (Program.encode PrivateKeyCopy.code).length + 2 * (Program.encode program).length + 2) +
    (2 * (initialPc + horizon * (PrivateKeyCopy.code.addressCap + program.addressCap + 1)) +
      18 * (initialCells + horizon) + 32)

theorem encoded_peak (program : Program) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : ResponseHandoff.Control) (hTarget : target ∈ (eval program elapsed start).support) :
    (completeEncoding.encode (PrivateKeyCopy.code, program, target)).length ≤
      bound program (responderPc start) (PrivacyStorage.responderCells start) horizon := by
  have hp := TimedExecution.ResourceGrowth.prefix_bound (step program) responderPc
    (PrivateKeyCopy.code.addressCap + program.addressCap + 1) (pc_step program) horizon elapsed hElapsed start target hTarget
  have hc := TimedExecution.ResourceGrowth.prefix_bound (step program) PrivacyStorage.responderCells
    1 (cells_step program) horizon elapsed hElapsed start target hTarget
  have hl := PrivacyEncoding.responder_length target
  have hr : (PrivacyEncoding.responder.encode target).length ≤
      2 * (responderPc start + horizon * (PrivateKeyCopy.code.addressCap + program.addressCap + 1)) +
        18 * (PrivacyStorage.responderCells start + horizon) + 32 := by omega
  rw [complete_length]
  exact Nat.add_le_add_left hr _

theorem bound_polynomial (program : Program) {initialPc initialCells horizon : Nat → Nat}
    (hPc : PolynomiallyBounded initialPc) (hCells : PolynomiallyBounded initialCells)
    (hTime : PolynomiallyBounded horizon) :
    PolynomiallyBounded (fun n => bound program (initialPc n) (initialCells n) (horizon n)) := by
  have hp := hPc.add (hTime.mul (PolynomiallyBounded.const
    (PrivateKeyCopy.code.addressCap + program.addressCap + 1)))
  have hc := hCells.add hTime
  exact (PolynomiallyBounded.const
    (2 * (Program.encode PrivateKeyCopy.code).length + 2 * (Program.encode program).length + 2)).add
      ((((PolynomiallyBounded.const 2).mul hp).add ((PolynomiallyBounded.const 18).mul hc)).add
        (PolynomiallyBounded.const 32))

end Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram
