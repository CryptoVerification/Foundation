import Foundation.Crypto.Semantics.Oracle.OneUseCallerCertificate
import Foundation.Crypto.Semantics.Oracle.OneUseProgramInitialization

/-! Actual native key generation followed by a caller certified at the
logical query level. Observation is made only after the complete physical
run. Its relation to the logical result is an explicit proof obligation. -/
namespace CryptoOracle.Interactive.OneUseCallerInitialization
open Foundation.Probability Foundation.Symmetric TimedExecution OneUseSourceRounds
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (caller : Configuration State) (width : Nat)
    (certificates : ∀ key : Bits width, CallerCertificate stateSize code oracle key.toList [] caller)
    (cap : Nat) (hCap : ∀ key, (certificates key).physicalBudget ≤ cap)

noncomputable def complete :=
  OneUseProgramInitialization.complete Machine.OneTimePad.Prepared.listProcedure.code code oracle caller width
    (fun key => (certificates key).consumer) cap
    (fun key => by rw [CallerCertificate.consumer_budget]; exact hCap key)

theorem budget :
    (complete stateSize code oracle caller width certificates cap hCap).budget () = 6 * width + 5 + cap :=
  OneUseProgramInitialization.budget _ _ _ _ _ _ _ _

include hCap in
theorem run (horizon : Nat) (hBudget : 6 * width + 5 + cap ≤ horizon) :
    TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen
      Machine.OneTimePad.Prepared.listProcedure.code code oracle caller)
      horizon (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      (uniform (Bits width)).bind (fun key =>
        (TimedExecution.eval (callerStep code oracle key.toList []) (certificates key).logicalBound
          ⟨false, caller⟩).map (OneUseInitialization.Control.active ∘ embed (OneUseProgramInitialization.store key))) := by
  have h := OneUseProgramInitialization.run Machine.OneTimePad.Prepared.listProcedure.code code oracle caller width
    (fun key => (certificates key).consumer) cap
    (fun key => by rw [CallerCertificate.consumer_budget]; exact hCap key) horizon hBudget
  simp_rw [CallerCertificate.consumer_semantics] at h
  simpa only [PMF.map_comp, OneUseProgramInitialization.store] using h

include hCap in
/-- Arbitrary observation types are allowed, but the adapter must prove
which part of the native final state equals the logical observation. -/
theorem observed_run {Observed : Type v}
    (readPhysical : OneUseInitialization.Control State → Observed) (readLogical : Boundary State → Observed)
    (hRead : ∀ (key : Bits width) (source : Boundary State),
      readPhysical (.active (embed (OneUseProgramInitialization.store key) source)) = readLogical source)
    (horizon : Nat) (hBudget : 6 * width + 5 + cap ≤ horizon) :
    (TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen
      Machine.OneTimePad.Prepared.listProcedure.code code oracle caller)
      horizon (.initializing (.generating (Machine.Configuration.initial (List.replicate width true))))).map readPhysical =
      (uniform (Bits width)).bind (fun key =>
        (TimedExecution.eval (callerStep code oracle key.toList []) (certificates key).logicalBound
          ⟨false, caller⟩).map readLogical) := by
  rw [run stateSize code oracle caller width certificates cap hCap horizon hBudget, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, hRead]

end CryptoOracle.Interactive.OneUseCallerInitialization
