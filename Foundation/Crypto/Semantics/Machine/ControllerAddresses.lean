import Foundation.Crypto.Semantics.Machine.ControllerEncoding
import Foundation.Crypto.Semantics.Machine.ControlStorage

/-! Native address growth through export and initialization controllers.
Transitions that discard native control reset the address measure to zero. -/
namespace Machine.ControllerEncoding
open Foundation.Probability

theorem export_pc_step (code : Program) (start next : ResponseExport.Control)
    (h : next ∈ (ResponseExport.step code start).support) :
    exportPc next ≤ exportPc start + (code.addressCap + 1) := by
  cases start with
  | running machine =>
      cases hh : machine.halted with
      | true =>
          simp [ResponseExport.step, hh, PMF.mem_support_pure_iff] at h
          subst next
          simp [exportPc]
      | false =>
          simp only [ResponseExport.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
          obtain ⟨target, hTarget, rfl⟩ := h
          exact Machine.pc_le_of_support code machine target hTarget
  | rewinding tape =>
      cases ht : tape.left <;> simp [ResponseExport.step, ht, PMF.mem_support_pure_iff] at h <;>
        subst next <;> simp [exportPc]
  | collecting tape reversed =>
      cases hc : tape.current <;> simp [ResponseExport.step, hc, PMF.mem_support_pure_iff] at h <;>
        subst next <;> simp [exportPc]
  | reversing remaining packet =>
      cases remaining <;> simp [ResponseExport.step, PMF.mem_support_pure_iff] at h <;>
        subst next <;> simp [exportPc]
  | returned packet =>
      simp [ResponseExport.step, PMF.mem_support_pure_iff] at h
      subst next
      simp [exportPc]

theorem initialization_pc_step (code : Program) (start next : PrivateInitialization.Control)
    (h : next ∈ (PrivateInitialization.step code start).support) :
    initializationPc next ≤ initializationPc start + (code.addressCap + 1) := by
  cases start with
  | generating machine =>
      cases hh : machine.halted with
      | true =>
          simp [PrivateInitialization.step, hh, PMF.mem_support_pure_iff] at h
          subst next
          simp [initializationPc]
      | false =>
          simp only [PrivateInitialization.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
          obtain ⟨target, hTarget, rfl⟩ := h
          exact Machine.pc_le_of_support code machine target hTarget
  | rewinding tape =>
      cases ht : tape.left <;> simp [PrivateInitialization.step, ht, PMF.mem_support_pure_iff] at h <;>
        subst next <;> simp [initializationPc]
  | ready tape =>
      simp [PrivateInitialization.step, PMF.mem_support_pure_iff] at h
      subst next
      simp [initializationPc]

end Machine.ControllerEncoding
