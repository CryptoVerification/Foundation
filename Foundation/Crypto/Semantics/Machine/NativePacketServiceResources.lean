import Foundation.Crypto.Semantics.Machine.NativePacketService
import Foundation.Crypto.Semantics.Machine.CellResponseExportResources
import Foundation.Crypto.Semantics.Machine.StructuredCodeEncoding
import Foundation.Crypto.Semantics.ResourceGrowth

/-! Faithful storage of request loading, native computation and physical
packet export. A linear local size bound controls every supported prefix,
including arbitrary represented padding and malformed control states. -/
namespace Machine.NativePacketService.Resources
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def fields := (FiniteBitEncoding.bitstring.prod ConfigurationEncoding.tape).sum
  ((FiniteBitEncoding.bitstring.prod ConfigurationEncoding.tape).sum
    (ConfigurationEncoding.tape.sum (ConfigurationEncoding.configuration.sum ControllerEncoding.responseExport)))

def encoding : FiniteBitEncoding Control where
  encode := fun state => fields.encode (match state with
    | .loading rest tape => .inl (rest, tape)
    | .advancing rest tape => .inr (.inl (rest, tape))
    | .rewinding tape => .inr (.inr (.inl tape))
    | .prepared machine => .inr (.inr (.inr (.inl machine)))
    | .executing component => .inr (.inr (.inr (.inr component))))
  decode := fun raw => (fields.decode raw).map fun state => match state with
    | .inl (rest, tape) => .loading rest tape
    | .inr (.inl (rest, tape)) => .advancing rest tape
    | .inr (.inr (.inl tape)) => .rewinding tape
    | .inr (.inr (.inr (.inl machine))) => .prepared machine
    | .inr (.inr (.inr (.inr component))) => .executing component
  decode_encode := by intro state; cases state <;> simp [fields.decode_encode]

def extent : Control → Nat
  | .loading rest tape | .advancing rest tape => max rest.length tape.cells
  | .rewinding tape => tape.cells
  | .prepared machine => ControllerExtent.machine machine
  | .executing component => ControllerExtent.exportExtent component

def pc : Control → Nat
  | .prepared machine => machine.pc
  | .executing component => ControllerEncoding.exportPc component
  | _ => 0

def size (state : Control) : Nat := max 1 (max (pc state) (extent state))

theorem step_extent (code : Program) (start next : Control)
    (h : next ∈ (step code start).support) : extent next ≤ extent start + 1 := by
  cases start with
  | loading rest tape =>
      cases rest <;> simp [step, PMF.mem_support_pure_iff] at h <;> subst next <;>
        simp [extent, Tape.cells_write] <;> omega
  | advancing rest tape =>
      simp [step, PMF.mem_support_pure_iff] at h
      subst next
      have ht := Tape.cells_moveRight_le tape
      simp only [extent]
      omega
  | rewinding tape =>
      cases hl : tape.left <;> simp [step, hl, PMF.mem_support_pure_iff] at h <;> subst next
      · simp only [extent, ControllerExtent.machine, Tape.cells, List.length_nil]
        omega
      · exact Tape.cells_moveLeft_le tape
  | prepared machine => simp [step, PMF.mem_support_pure_iff] at h; subst next; simp [extent, ControllerExtent.exportExtent]
  | executing component =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨after, ha, rfl⟩ := h
      exact CellResponseExport.Resources.step_extent code component after ha

theorem step_pc (code : Program) (start next : Control)
    (h : next ∈ (step code start).support) : pc next ≤ pc start + (code.addressCap + 1) := by
  cases start with
  | loading rest tape => cases rest <;> simp [step, PMF.mem_support_pure_iff] at h <;> subst next <;> simp [pc]
  | advancing rest tape => simp [step, PMF.mem_support_pure_iff] at h; subst next; simp [pc]
  | rewinding tape => cases hl : tape.left <;> simp [step, hl, PMF.mem_support_pure_iff] at h <;> subst next <;> simp [pc]
  | prepared machine => simp [step, PMF.mem_support_pure_iff] at h; subst next; simp [pc, ControllerEncoding.exportPc]
  | executing component =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨after, ha, rfl⟩ := h
      exact CellResponseExport.Resources.step_pc code component after ha

theorem step_size (code : Program) (start next : Control)
    (h : next ∈ (step code start).support) : size next ≤ size start + (code.addressCap + 1) := by
  have hp := step_pc code start next h
  have he := step_extent code start next h
  simp only [size]
  omega

theorem encoding_length (state : Control) :
    (encoding.encode state).length ≤ 76 * size state + 60 := by
  have he : extent state ≤ size state := by simp only [size]; omega
  have hp : pc state ≤ size state := by simp only [size]; omega
  cases state with
  | loading rest tape =>
      have ht := ConfigurationEncoding.tape_length_le tape
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inl_length,
        FiniteBitEncoding.prod_encode_length, FiniteBitEncoding.bitstring, id_eq]
      simp only [extent, pc] at he hp
      omega
  | advancing rest tape =>
      have ht := ConfigurationEncoding.tape_length_le tape
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.sum_encode_inl_length,
        FiniteBitEncoding.prod_encode_length, FiniteBitEncoding.bitstring, id_eq]
      simp only [extent, pc] at he hp
      omega
  | rewinding tape =>
      have ht := ConfigurationEncoding.tape_length_le tape
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.sum_encode_inl_length]
      simp only [extent] at he
      omega
  | prepared machine =>
      have hm := ConfigurationEncoding.configuration_length_le machine
      have hc := ControllerExtent.machine_cells machine
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.sum_encode_inl_length]
      simp only [extent, pc] at he hp
      omega
  | executing component =>
      have hm := ControllerEncoding.export_length_le component
      have hc := ControllerExtent.export_cells component
      simp only [encoding, fields, FiniteBitEncoding.sum_encode_inr_length]
      simp only [extent, pc] at he hp
      omega

def completeEncoding : FiniteBitEncoding (Program × Control) := StructuredCodeEncoding.program.prod encoding

def bitBound (code : Program) (initialSize horizon : Nat) : Nat :=
  2 * (StructuredCodeEncoding.program.encode code).length +
    76 * (initialSize + horizon * (code.addressCap + 1)) + 61

theorem peak (code : Program) (start : Control) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (target : Control) (hTarget : target ∈ (eval (step code) elapsed start).support) :
    (completeEncoding.encode (code, target)).length ≤ bitBound code (size start) horizon := by
  have hs := ResourceGrowth.prefix_bound (step code) size (code.addressCap + 1) (step_size code)
    horizon elapsed hElapsed start target hTarget
  have he := encoding_length target
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length]
  unfold bitBound
  omega

theorem bitBound_polynomial (code : Program) {initialSize horizon : Nat → Nat}
    (hSize : PolynomiallyBounded initialSize) (hTime : PolynomiallyBounded horizon) :
    PolynomiallyBounded (fun n => bitBound code (initialSize n) (horizon n)) :=
  (((PolynomiallyBounded.const (2 * (StructuredCodeEncoding.program.encode code).length)).add
    ((PolynomiallyBounded.const 76).mul (hSize.add
      (hTime.mul (PolynomiallyBounded.const (code.addressCap + 1)))))).add (PolynomiallyBounded.const 61))

end Machine.NativePacketService.Resources
