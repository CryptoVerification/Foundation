import Foundation.Crypto.Semantics.Oracle.EncodedStorage

/-! Address bounds for enclosing machines that execute public actions but
intercept oracle calls. The bounds follow from real source transitions. -/
namespace CryptoOracle.Interactive.EncodedStorage
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

private noncomputable def emptyOracle : BitOracle Unit := fun _ _ => PMF.pure ((), [])

theorem deterministic_action_pc (code : Code) (control : Control) (target : Configuration Unit)
    (hRunning : Reification.terminal control = false)
    (hAction : Reification.action code control = .deterministic target) :
    ConfigurationEncoding.pc target.control ≤ ConfigurationEncoding.pc control + (addressCap code + 1) := by
  have hm : ({ state := (), control := target.control, reverseTrace := [] } : Configuration Unit) ∈
      (Reification.timedStep code emptyOracle ⟨(), control, []⟩).support := by
    simp [Reification.timedStep, hRunning, Reification.perform, hAction]
  exact pc_step code emptyOracle _ _ hm

theorem random_action_pc (code : Code) (control : Control) (zero one : Configuration Unit)
    (hRunning : Reification.terminal control = false)
    (hAction : Reification.action code control = .random zero one) (bit : Bool) :
    ConfigurationEncoding.pc (if bit then one.control else zero.control) ≤
      ConfigurationEncoding.pc control + (addressCap code + 1) := by
  have hm : (⟨(), (if bit then one.control else zero.control), []⟩ : Configuration Unit) ∈
      (Reification.timedStep code emptyOracle ⟨(), control, []⟩).support := by
    simp only [Reification.timedStep, hRunning, Bool.false_eq_true, ↓reduceIte,
      Reification.perform, hAction, PMF.mem_support_map_iff]
    exact ⟨bit, PMF.mem_support_uniformOfFintype bit, rfl⟩
  exact pc_step code emptyOracle _ _ hm

theorem oracle_action_pc (code : Code) (control : Control) (machine : Machine.Configuration) (request : List Bool)
    (hRunning : Reification.terminal control = false)
    (hAction : Reification.action code control = .oracleCall machine request) :
    machine.pc ≤ ConfigurationEncoding.pc control + (addressCap code + 1) := by
  have hm : (⟨(), .loading machine [] {}, [(request, [])]⟩ : Configuration Unit) ∈
      (Reification.timedStep code emptyOracle ⟨(), control, []⟩).support := by
    simp [Reification.timedStep, hRunning, Reification.perform, hAction, emptyOracle]
  exact pc_step code emptyOracle _ _ hm

end CryptoOracle.Interactive.EncodedStorage
