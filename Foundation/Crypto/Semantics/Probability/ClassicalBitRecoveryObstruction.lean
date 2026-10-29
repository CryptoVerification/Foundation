import Foundation.Crypto.Semantics.Probability.ClassicalBitRoundtripKernel
import Foundation.Crypto.Semantics.Probability.KernelRecovery

/-! The fixed forward maximal kernel merges two supported source results.
No reverse kernel receiving only the intermediate result can recover every
supported source. Alternative forward kernels or extra state are not excluded. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction
open Foundation.Probability
open scoped ENNReal
noncomputable section
abbrev Result := Fin 5 × Bool

def forward (message : Bool) : Result → PMF Result :=
  FiniteMaximalCoupling.kernel (Roundtrip.p message) (Roundtrip.q message)

theorem shared_from_zero_real (message : Bool) :
    (forward message (0,message) (1,message)).toReal = 25 / 296 := by
  rw [forward, Roundtrip.kernel_real]
  simp only [FiniteMaximalCoupling.mass, FiniteMaximalCoupling.common, FiniteMaximalCoupling.left,
    FiniteMaximalCoupling.right, Roundtrip.forward_residual, Roundtrip.p_real, Roundtrip.q_real]
  cases message <;> norm_num [Roundtrip.sourceCount, Roundtrip.targetCount, Fin.ext_iff]

theorem shared_from_two_real (message : Bool) :
    (forward message (2,!message) (1,message)).toReal = 85 / 1184 := by
  rw [forward, Roundtrip.kernel_real]
  simp only [FiniteMaximalCoupling.mass, FiniteMaximalCoupling.common, FiniteMaximalCoupling.left,
    FiniteMaximalCoupling.right, Roundtrip.forward_residual, Roundtrip.p_real, Roundtrip.q_real]
  cases message <;> norm_num [Roundtrip.sourceCount, Roundtrip.targetCount, Fin.ext_iff]

theorem shared_from_zero (message : Bool) : (1,message) ∈ (forward message (0,message)).support := by
  apply (PMF.mem_support_iff _ _).mpr
  intro h
  have hr := shared_from_zero_real message
  rw [h] at hr
  norm_num at hr

theorem shared_from_two (message : Bool) : (1,message) ∈ (forward message (2,!message)).support := by
  apply (PMF.mem_support_iff _ _).mpr
  intro h
  have hr := shared_from_two_real message
  rw [h] at hr
  norm_num at hr

theorem two_source_supported (message : Bool) : (2,!message) ∈ (Roundtrip.p message).support := by
  apply (PMF.mem_support_iff _ _).mpr
  intro h
  have hr := Roundtrip.p_real message (2,!message)
  rw [h] at hr
  cases message <;> norm_num [Roundtrip.sourceCount] at hr

theorem no_reverse (message : Bool) :
    ¬ ∃ reverse, KernelRecovery.RecoversOn (forward message) reverse
      (fun result => result ∈ (Roundtrip.p message).support) := by
  apply KernelRecovery.common_output_no_recovery (forward message) _
    (0,message) (2,!message) (Roundtrip.source_supported message) (two_source_supported message)
    (by intro same; exact (by decide : (0 : Fin 5) ≠ 2) (congrArg Prod.fst same))
    (1,message) (shared_from_zero message) (shared_from_two message)

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryObstruction
