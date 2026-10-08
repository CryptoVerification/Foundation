import Foundation.Crypto.Semantics.Oracle.OneUseRoundCertificate
import Foundation.Crypto.Semantics.Oracle.OneUseProgramInitialization

/-! A family of proved finite-round callers is selected by the actual uniform
native-generated key. Whole execution includes generation, all rounds and a
real caller terminal. No concrete bit-width or query transcript is fixed. -/
namespace CryptoOracle.Interactive.OneUseInitializedRounds
open Foundation.Probability Foundation.Symmetric TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}
    (code : Code) (oracle : BitOracle State) (caller : Configuration State) (width : Nat)
    (certificates : ∀ key : Bits width, OneUseSourceRounds.Certificate code oracle key.toList [] caller)
    (cap : Nat) (hCap : ∀ key, (certificates key).count * (certificates key).bound ≤ cap)

noncomputable def consumers := fun key => (certificates key).consumer

noncomputable def complete :=
  OneUseProgramInitialization.complete Machine.OneTimePad.Prepared.listProcedure.code code oracle caller width
    (consumers code oracle caller width certificates) cap
    (fun key => by
      change (certificates key).consumer.execution.budget () ≤ cap
      rw [OneUseSourceRounds.Certificate.consumer_budget]
      exact hCap key)

theorem budget :
    (complete code oracle caller width certificates cap hCap).budget () = 6 * width + 5 + cap :=
  OneUseProgramInitialization.budget _ _ _ _ _ _ _ _

include hCap in
/-- Final joint physical distribution: each real generated key selects its
own certified adaptive caller, with the same finite instruction list. -/
theorem run (horizon : Nat) (hBudget : 6 * width + 5 + cap ≤ horizon) :
    TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen
      Machine.OneTimePad.Prepared.listProcedure.code code oracle caller)
      horizon (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      (uniform (Bits width)).bind (fun key =>
        (TimedExecution.eval (OneUseSourceRounds.round code oracle key.toList [] (certificates key).fuel
          (certificates key).cap (certificates key).capProof).semantics
          (certificates key).count (OneUseSourceRounds.Boundary.mk false caller)).map
            (OneUseInitialization.Control.active ∘
              OneUseSourceRounds.embed (OneUseProgramInitialization.store key))) := by
  have h := OneUseProgramInitialization.run Machine.OneTimePad.Prepared.listProcedure.code code oracle caller width
    (consumers code oracle caller width certificates) cap
    (fun key => by
      change (certificates key).consumer.execution.budget () ≤ cap
      rw [OneUseSourceRounds.Certificate.consumer_budget]
      exact hCap key) horizon hBudget
  simp only [consumers] at h
  simp_rw [OneUseSourceRounds.Certificate.consumer_semantics] at h
  simp only [PMF.map_comp] at h
  convert h using 1 <;> rfl

end CryptoOracle.Interactive.OneUseInitializedRounds
