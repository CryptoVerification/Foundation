import Foundation.Crypto.Semantics.Oracle.OneUseProgramInitialization

/-! Observations of a completed native caller with an arbitrary native
handler. The consumer supplies real physical entry/exit, time and termination
proofs. Observation is a mathematical projection, not a charged host action. -/
namespace CryptoOracle.Interactive.OneUseProgramInitialization
open Foundation.Probability Foundation.Symmetric TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Observed : Type v}
variable (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Configuration State) (width : Nat)
    (consumers : ∀ key : Bits width, OneUseProgramContract.Consumer native code oracle caller (store key))
    (cap : Nat) (hCap : ∀ key, (consumers key).execution.budget () ≤ cap)

include hCap in
/-- Key-conditional observation laws of consumer contracts compose with
actual native key generation into a whole-machine observation law. -/
theorem observed_run
    (readPhysical : OneUseInitialization.Control State → Observed)
    (keyGame : Bits width → PMF Observed)
    (hGame : ∀ key, ((consumers key).execution.semantics ()).map
      (readPhysical ∘ OneUseInitialization.Control.active) = keyGame key)
    (horizon : Nat) (hBudget : 6 * width + 5 + cap ≤ horizon) :
    (TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen native code oracle caller)
      horizon (.initializing (.generating (Machine.Configuration.initial (List.replicate width true))))).map readPhysical =
      (uniform (Bits width)).bind keyGame := by
  rw [run native code oracle caller width consumers cap hCap horizon hBudget, PMF.map_bind]
  simp only [PMF.map_comp, hGame]

/-- Retain correlation between observed returns and actual charged costs.
The key generator's duration is not replaced by its upper bound. -/
theorem observed_costed
    (readPhysical : OneUseInitialization.Control State → Observed) :
    ((complete native code oracle caller width consumers cap hCap).costed ()).map
      (fun result => (readPhysical (.active result.1.2), result.2)) =
      ((OneUseBitInitialization.initialization native code oracle caller width).costed ()).bind
        (fun generated => ((consumers generated.1.1).execution.costed ()).map
          (fun returned => (readPhysical (.active returned.1), generated.2 + returned.2))) := by
  rw [costed, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

end CryptoOracle.Interactive.OneUseProgramInitialization
