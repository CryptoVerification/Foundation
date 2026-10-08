import Foundation.Crypto.Semantics.Oracle.PrivateControllerEncoding
import Foundation.Crypto.Semantics.Oracle.EncodedStorage
import Foundation.Crypto.Semantics.Machine.ControllerAddresses

/-! Address growth in real callback and request controllers. Saved caller
addresses are transferred to callback source states; they are not reset or
treated as uncharged host values. -/
namespace CryptoOracle.Interactive.PrivateControllerEncoding
open Machine Foundation.Probability
universe u
variable {State : Type u}

theorem callback_pc_step (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)
    (start next : NativeCallback.Control State)
    (h : next ∈ (NativeCallback.step native code oracle saved state trace request start).support) :
    callbackPc next ≤ max saved.pc (callbackPc start) + (native.addressCap + EncodedStorage.addressCap code + 1) := by
  cases start with
  | responding component =>
      cases component with
      | returned packet =>
          simp [NativeCallback.step, PMF.mem_support_pure_iff] at h
          subst next
          simp [callbackPc, NativeCallback.loading, ConfigurationEncoding.pc]
          omega
      | running machine =>
          simp only [NativeCallback.step, PMF.mem_support_map_iff] at h
          obtain ⟨target, ht, rfl⟩ := h
          have hb := ControllerEncoding.export_pc_step native (.running machine) target ht
          simp only [callbackPc] at ⊢
          omega
      | rewinding tape =>
          simp only [NativeCallback.step, PMF.mem_support_map_iff] at h
          obtain ⟨target, ht, rfl⟩ := h
          have hb := ControllerEncoding.export_pc_step native (.rewinding tape) target ht
          simp only [callbackPc] at ⊢
          omega
      | collecting tape reversed =>
          simp only [NativeCallback.step, PMF.mem_support_map_iff] at h
          obtain ⟨target, ht, rfl⟩ := h
          have hb := ControllerEncoding.export_pc_step native (.collecting tape reversed) target ht
          simp only [callbackPc] at ⊢
          omega
      | reversing remaining packet =>
          simp only [NativeCallback.step, PMF.mem_support_map_iff] at h
          obtain ⟨target, ht, rfl⟩ := h
          have hb := ControllerEncoding.export_pc_step native (.reversing remaining packet) target ht
          simp only [callbackPc] at ⊢
          omega
  | source frame =>
      simp only [NativeCallback.step, PMF.mem_support_map_iff] at h
      obtain ⟨target, ht, rfl⟩ := h
      have hb := EncodedStorage.pc_step code oracle frame target ht
      simp only [callbackPc]
      omega

theorem checked_pc_step (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)
    (start next : CheckedCallback.Control State)
    (h : next ∈ (CheckedCallback.step native code oracle saved state trace request start).support) :
    checkedPc next ≤ max saved.pc (checkedPc start) + (native.addressCap + EncodedStorage.addressCap code + 1) := by
  cases start with
  | preparing preparation =>
      cases preparation with
      | preparing pair =>
          cases pair <;> simp only [CheckedCallback.step] at h
          all_goals first
            | (rw [PMF.mem_support_pure_iff] at h; subst next; simp [checkedPc, ControllerEncoding.exportPc])
            | (rw [PMF.mem_support_map_iff] at h; obtain ⟨target, _, rfl⟩ := h; simp [checkedPc])
      | failure recovery =>
          cases recovery <;> simp only [CheckedCallback.step] at h
          all_goals first
            | (rw [PMF.mem_support_pure_iff] at h; subst next; simp [checkedPc, callbackPc, ControllerEncoding.exportPc])
            | (rw [PMF.mem_support_map_iff] at h; obtain ⟨target, _, rfl⟩ := h; simp [checkedPc])
  | computing first second component =>
      cases component <;> simp only [CheckedCallback.step] at h
      all_goals first
        | (rw [PMF.mem_support_pure_iff] at h; subst next; simp [checkedPc])
        | (rw [PMF.mem_support_map_iff] at h; obtain ⟨target, ht, rfl⟩ := h
           have hb := ControllerEncoding.export_pc_step native _ target ht
           simp only [checkedPc]; omega)
  | tagging first second packet =>
      cases packet <;> simp only [CheckedCallback.step] at h
      all_goals first
        | (rw [PMF.mem_support_pure_iff] at h; subst next; simp [checkedPc, callbackPc, ControllerEncoding.exportPc])
        | (rw [PMF.mem_support_map_iff] at h; obtain ⟨target, _, rfl⟩ := h; simp [checkedPc])
  | calling first second callback =>
      rw [CheckedCallback.step, PMF.mem_support_map_iff] at h
      obtain ⟨target, ht, rfl⟩ := h
      have hb := callback_pc_step [] code oracle saved state trace request callback target ht
      simp only [checkedPc]
      simp only [Program.addressCap] at hb
      omega

def sourceMaxPc : OneUseSource.Control State → Nat
  | .source _ _ frame => ConfigurationEncoding.pc frame.control
  | .handling _ saved _ _ _ handler => max saved.pc (checkedPc handler)

theorem sourcePc_le_twice (c : OneUseSource.Control State) : sourcePc c ≤ 2 * sourceMaxPc c := by
  cases c <;> simp only [sourcePc, sourceMaxPc] <;> omega

private theorem mapped_handling_pc (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (handler : CheckedCallback.Control State)
    (next : OneUseSource.Control State)
    (h : next ∈ ((CheckedCallback.step native code oracle saved state trace request handler).map
      (.handling spent saved state trace request)).support) :
    sourceMaxPc next ≤ max saved.pc (checkedPc handler) + (native.addressCap + EncodedStorage.addressCap code + 1) := by
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨target, ht, rfl⟩ := h
  have hb := checked_pc_step native code oracle saved state trace request handler target ht
  simp only [sourceMaxPc]
  omega

theorem source_max_pc_step (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (start next : OneUseSource.Control State)
    (h : next ∈ (OneUseSource.step native code oracle start).support) :
    sourceMaxPc next ≤ sourceMaxPc start + (native.addressCap + EncodedStorage.addressCap code + 1) := by
  cases start with
  | source spent key frame =>
      cases hc : frame.control <;> simp only [OneUseSource.step, hc] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨target, ht, rfl⟩ := h
           have hb := EncodedStorage.pc_step code oracle frame target ht
           simp only [sourceMaxPc]
           omega)
        | (rw [PMF.mem_support_pure_iff] at h
           subst next
           cases spent <;> simp [sourceMaxPc, checkedPc, hc, ConfigurationEncoding.pc])
  | handling spent saved state trace request handler =>
      cases handler with
      | preparing preparation =>
          cases preparation with
          | preparing pair =>
              cases pair <;> cases spent <;> simp only [OneUseSource.step, Bool.false_eq_true, ↓reduceIte] at h
              all_goals first
                | (rw [PMF.mem_support_pure_iff] at h; subst next;
                   simp [sourceMaxPc, checkedPc, ControllerEncoding.exportPc])
                | (exact mapped_handling_pc native code oracle _ saved state trace request _ next h)
          | failure recovery =>
              simp only [OneUseSource.step] at h
              exact mapped_handling_pc native code oracle _ saved state trace request _ next h
      | computing first second component =>
          simp only [OneUseSource.step] at h
          exact mapped_handling_pc native code oracle _ saved state trace request _ next h
      | tagging first second packet =>
          simp only [OneUseSource.step] at h
          exact mapped_handling_pc native code oracle _ saved state trace request _ next h
      | calling first second callback =>
          cases callback with
          | responding component =>
              simp only [OneUseSource.step] at h
              exact mapped_handling_pc native code oracle _ saved state trace request _ next h
          | source frame =>
              rcases frame with ⟨currentState, currentControl, currentTrace⟩
              cases currentControl <;> simp only [OneUseSource.step] at h
              all_goals first
                | (rw [PMF.mem_support_pure_iff] at h; subst next;
                   simp only [sourceMaxPc, checkedPc, callbackPc, ConfigurationEncoding.pc]; omega)
                | (exact mapped_handling_pc native code oracle _ saved state trace request _ next h)

def initializationMaxPc (caller : Configuration State) : OneUseInitialization.Control State → Nat
  | .initializing component => max (ConfigurationEncoding.pc caller.control) (ControllerEncoding.initializationPc component)
  | .active component => sourceMaxPc component

theorem initializationPc_le_twice (caller : Configuration State) (c : OneUseInitialization.Control State) :
    initializationPc caller c ≤ 2 * initializationMaxPc caller c := by
  cases c with
  | initializing component => simp only [initializationPc, initializationMaxPc]; omega
  | active component => exact sourcePc_le_twice component

theorem initialization_max_pc_step (generator native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State)
    (start next : OneUseInitialization.Control State)
    (h : next ∈ (OneUseInitialization.step generator native code oracle caller start).support) :
    initializationMaxPc caller next ≤ initializationMaxPc caller start +
      (generator.addressCap + native.addressCap + EncodedStorage.addressCap code + 1) := by
  cases start with
  | initializing component =>
      cases component with
      | ready key =>
          simp [OneUseInitialization.step, PMF.mem_support_pure_iff] at h
          subst next
          simp [initializationMaxPc, sourceMaxPc, ControllerEncoding.initializationPc]
      | generating machine =>
          simp only [OneUseInitialization.step, PMF.mem_support_map_iff] at h
          obtain ⟨target, ht, rfl⟩ := h
          have hb := ControllerEncoding.initialization_pc_step generator (.generating machine) target ht
          simp only [initializationMaxPc]
          omega
      | rewinding tape =>
          simp only [OneUseInitialization.step, PMF.mem_support_map_iff] at h
          obtain ⟨target, ht, rfl⟩ := h
          have hb := ControllerEncoding.initialization_pc_step generator (.rewinding tape) target ht
          simp only [initializationMaxPc]
          omega
  | active component =>
      simp only [OneUseInitialization.step, PMF.mem_support_map_iff] at h
      obtain ⟨target, ht, rfl⟩ := h
      have hb := source_max_pc_step native code oracle component target ht
      simp only [initializationMaxPc]
      omega

end CryptoOracle.Interactive.PrivateControllerEncoding
