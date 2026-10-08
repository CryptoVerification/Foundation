import Foundation.Crypto.Semantics.Oracle.ControllerExtentExecution

/-! Reuse source-controller growth when an enclosing machine intercepts
oracle calls but executes deterministic and random source actions directly. -/
namespace CryptoOracle.Interactive.ControllerExtent
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

private noncomputable def emptyOracle : BitOracle Unit := fun _ _ => PMF.pure ((), [])

private theorem empty_bound : ∀ state request result,
    result ∈ (emptyOracle state request).support →
      (fun _ : Unit => 0) result.1 ≤ (fun _ : Unit => 0) state + 0 ∧ result.2.length ≤ 0 := by
  intro state request result h
  simp only [emptyOracle, PMF.mem_support_pure_iff] at h
  subst result
  simp

theorem deterministic_action (code : Code) (control : Control) (target : Configuration Unit)
    (hRunning : Reification.terminal control = false)
    (hAction : Reification.action code control = .deterministic target) :
    controlExtent target.control ≤ controlExtent control + 2 := by
  have hm : ({ state := (), control := target.control, reverseTrace := [] } : Configuration Unit) ∈
      (Reification.timedStep code emptyOracle ⟨(), control, []⟩).support := by
    simp [Reification.timedStep, hRunning, Reification.perform, hAction]
  have hb := public_step (fun _ : Unit => 0) code emptyOracle 0 0 empty_bound _ _ hm
  simpa [frameExtent, traceExtent] using hb

theorem random_action (code : Code) (control : Control) (zero one : Configuration Unit)
    (hRunning : Reification.terminal control = false)
    (hAction : Reification.action code control = .random zero one) (bit : Bool) :
    controlExtent (if bit then one.control else zero.control) ≤ controlExtent control + 2 := by
  have hm : (⟨(), (if bit then one.control else zero.control), []⟩ : Configuration Unit) ∈
      (Reification.timedStep code emptyOracle ⟨(), control, []⟩).support := by
    simp only [Reification.timedStep, hRunning, Bool.false_eq_true, ↓reduceIte,
      Reification.perform, hAction, PMF.mem_support_map_iff]
    exact ⟨bit, PMF.mem_support_uniformOfFintype bit, rfl⟩
  have hb := public_step (fun _ : Unit => 0) code emptyOracle 0 0 empty_bound _ _ hm
  simpa [frameExtent, traceExtent] using hb

end CryptoOracle.Interactive.ControllerExtent
