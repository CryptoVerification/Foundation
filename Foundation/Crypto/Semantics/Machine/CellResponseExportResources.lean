import Foundation.Crypto.Semantics.Machine.CellResponseExport
import Foundation.Crypto.Semantics.Machine.ControllerExtent
import Foundation.Crypto.Semantics.Machine.ControllerEncoding
import Foundation.Crypto.Semantics.Machine.NativeEncodedResources

/-! Cell-aware physical export obeys the same storage-growth bounds as the
other native controllers. Actual represented blank cells are counted. -/
namespace Machine.CellResponseExport.Resources
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

abbrev extent := ControllerExtent.exportExtent
abbrev pc := ControllerEncoding.exportPc

theorem step_extent (code : Program) (start next : Control)
    (h : next ∈ (CellResponseExport.step code start).support) : extent next ≤ extent start + 1 := by
  cases start with
  | running c =>
      by_cases hh : c.halted = true
      · simp [CellResponseExport.step, hh] at h
        subst next
        simp [extent, ControllerExtent.exportExtent, ControllerExtent.machine]
        omega
      · simp only [CellResponseExport.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨value, hv, rfl⟩ := h
        exact ControllerExtent.native_bound code c value hv
  | rewinding tape =>
      by_cases hl : (tape.left[0]?.getD none).isSome = true
      · simp [CellResponseExport.step, hl] at h
        subst next
        exact Tape.cells_moveLeft_le tape
      · simp [CellResponseExport.step, hl] at h
        subst next
        simp [extent, ControllerExtent.exportExtent]
  | collecting tape reversed =>
      cases hc : tape.current <;> simp [CellResponseExport.step, hc] at h <;> subst next
      · simp [extent, ControllerExtent.exportExtent]
        omega
      · have hb := Tape.cells_moveRight_le tape
        simp only [extent, ControllerExtent.exportExtent, List.length_cons]
        omega
  | reversing remaining response =>
      cases remaining <;> simp [CellResponseExport.step] at h <;> subst next <;>
        simp [extent, ControllerExtent.exportExtent] <;> omega
  | returned response => simp [CellResponseExport.step] at h; subst next; omega

theorem step_pc (code : Program) (start next : Control)
    (h : next ∈ (CellResponseExport.step code start).support) : pc next ≤ pc start + (code.addressCap + 1) := by
  cases start with
  | running c =>
      by_cases hh : c.halted = true
      · simp [CellResponseExport.step, hh] at h
        subst next
        simp [pc, ControllerEncoding.exportPc]
      · simp only [CellResponseExport.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨value, hv, rfl⟩ := h
        exact pc_le_of_support code c value hv
  | rewinding tape =>
      by_cases hl : (tape.left[0]?.getD none).isSome = true <;>
        simp [CellResponseExport.step, hl] at h <;> subst next <;> simp [pc, ControllerEncoding.exportPc]
  | collecting tape reversed =>
      cases hc : tape.current <;> simp [CellResponseExport.step, hc] at h <;> subst next <;>
        simp [pc, ControllerEncoding.exportPc]
  | reversing remaining packet =>
      cases remaining <;> simp [CellResponseExport.step] at h <;> subst next <;> simp [pc, ControllerEncoding.exportPc]
  | returned packet => simp [CellResponseExport.step] at h; subst next; omega

end Machine.CellResponseExport.Resources
