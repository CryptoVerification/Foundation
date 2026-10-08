import Foundation.Crypto.Logic.General.ObservedExecution
import Foundation.Crypto.Logic.General.OneUseContractObservedBackend
import Foundation.Crypto.Logic.General.Backends
import Foundation.Crypto.Semantics.Oracle.OneUseCallerInitialization

/-! Registration of arbitrary-width, caller-certified one-use execution.
The emitted code is a finite caller instruction list. Runtime inputs, logical
bounds, and observations are analysis data, never compiler instructions.
Observers describe a mathematical game; their host evaluation is not charged
as an instruction. The execution predicate charges actual native key generation
and the complete caller. It does not claim bit-encoded storage bounds. -/
namespace CryptoLogic.General.OneUseObservedBackend
open Foundation.Probability Foundation.Symmetric CryptoOracle.Interactive
open OneUseSourceRounds
universe u v
set_option backward.isDefEq.respectTransparency false

structure Profile (P : CryptoGoal.{u}) (State : Type v) where
  width : Nat → Nat
  stateSize : State → Nat
  oracle : ∀ n, P.Instance n → Bool → BitOracle State
  caller : ∀ n, P.Instance n → Bool → Configuration State
  logicalBound : Nat → Nat
  cap : Nat → Nat
  horizon : Nat → Nat
  readPhysical : ∀ n, P.Instance n → Bool → OneUseInitialization.Control State → Bool
  readLogical : ∀ n, P.Instance n → Bool → Boundary State → Bool

namespace Profile
variable {P : CryptoGoal.{u}} {State : Type v} (r : Profile P State)

def ExecutesWithin (F : InstanceFamily P) (code : CryptoOracle.Interactive.Code) : Prop :=
  PolynomiallyBounded r.horizon ∧ ∀ n side,
    (6 * r.width n + 5 + r.cap n ≤ r.horizon n) ∧
    (∃ certificates : ∀ key : Bits (r.width n),
      CallerCertificate r.stateSize code (r.oracle n (F n) side) key.toList [] (r.caller n (F n) side),
      (∀ key, (certificates key).physicalBudget ≤ r.cap n) ∧
      (∀ key, (certificates key).logicalBound = r.logicalBound n)) ∧
    (∀ (key : Bits (r.width n)) (source : Boundary State),
      r.readPhysical n (F n) side
        (.active (embed (OneUseProgramInitialization.store key) source)) =
          r.readLogical n (F n) side source)

noncomputable def nativeGame (F : InstanceFamily P) (code : CryptoOracle.Interactive.Code)
    (n : Nat) (side : Bool) : PMF Bool :=
  (TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen
    Machine.OneTimePad.Prepared.listProcedure.code code (r.oracle n (F n) side) (r.caller n (F n) side))
    (r.horizon n) (.initializing (.generating
      (Machine.Configuration.initial (List.replicate (r.width n) true))))).map (r.readPhysical n (F n) side)

noncomputable def logicalGame (F : InstanceFamily P) (code : CryptoOracle.Interactive.Code)
    (n : Nat) (side : Bool) : PMF Bool :=
  (uniform (Bits (r.width n))).bind (fun key =>
    (TimedExecution.eval (callerStep code (r.oracle n (F n) side) key.toList [])
      (r.logicalBound n) ⟨false, r.caller n (F n) side⟩).map (r.readLogical n (F n) side))

theorem nativeGame_eq (F : InstanceFamily P) (code : CryptoOracle.Interactive.Code)
    (hExec : r.ExecutesWithin F code) (n : Nat) (side : Bool) :
    r.nativeGame F code n side = r.logicalGame F code n side := by
  obtain ⟨hHorizon, ⟨certificates, hCap, hBound⟩, hRead⟩ := hExec.2 n side
  have h := OneUseCallerInitialization.observed_run r.stateSize code (r.oracle n (F n) side)
    (r.caller n (F n) side) (r.width n) certificates (r.cap n) hCap
    (r.readPhysical n (F n) side) (r.readLogical n (F n) side) hRead (r.horizon n) hHorizon
  simp_rw [hBound] at h
  exact h

/-- The logical caller adapter is an instance of the handler-independent
contract adapter; code and physical observation are unchanged. -/
noncomputable def toContract : OneUseContractObservedBackend.Profile P State where
  width := r.width
  oracle := r.oracle
  caller := r.caller
  cap := r.cap
  horizon := r.horizon
  readPhysical := r.readPhysical
  keyGame := fun code n publicInstance side key =>
    (TimedExecution.eval (callerStep code (r.oracle n publicInstance side) key.toList [])
      (r.logicalBound n) ⟨false, r.caller n publicInstance side⟩).map (r.readLogical n publicInstance side)

theorem toContract_executes (F : InstanceFamily P) (code : CryptoOracle.Interactive.Code)
    (hExec : r.ExecutesWithin F code) :
    r.toContract.ExecutesWithin Machine.OneTimePad.Prepared.listProcedure.code F code := by
  refine ⟨hExec.1, ?_⟩
  intro n side
  obtain ⟨hHorizon, ⟨certificates, hCap, hBound⟩, hRead⟩ := hExec.2 n side
  refine ⟨hHorizon, (fun key => (certificates key).consumer), ?_, ?_⟩
  · intro key
    rw [CallerCertificate.consumer_budget]
    exact hCap key
  · intro key
    rw [CallerCertificate.consumer_semantics, PMF.map_comp]
    change (TimedExecution.eval (callerStep code (r.oracle n (F n) side) key.toList [])
      (certificates key).logicalBound ⟨false, r.caller n (F n) side⟩).map
        (fun source => r.readPhysical n (F n) side
          (.active (embed (OneUseProgramInitialization.store key) source))) =
      (TimedExecution.eval (callerStep code (r.oracle n (F n) side) key.toList [])
        (r.logicalBound n) ⟨false, r.caller n (F n) side⟩).map (r.readLogical n (F n) side)
    simp only [hBound key, hRead]

theorem toContract_nativeGame (F : InstanceFamily P) (code : CryptoOracle.Interactive.Code) (n side) :
    r.toContract.nativeGame Machine.OneTimePad.Prepared.listProcedure.code F code n side =
      r.nativeGame F code n side := rfl

theorem toContract_logicalGame (F : InstanceFamily P) (code : CryptoOracle.Interactive.Code) (n side) :
    r.toContract.logicalGame F code n side = r.logicalGame F code n side := rfl

end Profile

variable {P : CryptoGoal.{u}} {State : Type v}

/-- The same registration works for any goal whose advantage is the stated
two-game probability gap. It does not assume the goal's security. -/
noncomputable def registration
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true))) :
    ObservedExecution Backends.system .interactive P where
  Resources := Profile P State
  ExecutesWithin := fun F code r => r.ExecutesWithin F code
  game := fun F code r => r.nativeGame F code
  modelGame := modelGame
  advantage_eq := hAdvantage

theorem realizes_of_logical
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))
    (F A) (code : CryptoOracle.Interactive.Code) (r : Profile P State)
    (hExec : r.ExecutesWithin F code)
    (hLogical : ∀ n side, r.logicalGame F code n side = modelGame F A n side) :
    (registration (State := State) modelGame hAdvantage).Realizes F A code r := by
  intro n side
  exact (r.nativeGame_eq F code hExec n side).trans (hLogical n side)

/-- Build a represented attack from caller stopping/resource proofs and a
logical game law. Native realization is derived, not an extra assumption. -/
def witness
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))
    (F A) (code : CryptoOracle.Interactive.Code) (r : Profile P State)
    (hExec : r.ExecutesWithin F code)
    (hLogical : ∀ n side, r.logicalGame F code n side = modelGame F A n side) :
    (registration (State := State) modelGame hAdvantage).object.Witness F A := by
  have hReal := realizes_of_logical modelGame hAdvantage F A code r hExec hLogical
  exact ⟨code, r, hExec, hReal, ⟨code, r, hExec, hReal⟩⟩

/-- Bounds established for the logical caller transfer to every represented
native attack, including actual key generation and query processing. -/
theorem secure_of_logical
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))
    (F : InstanceFamily P)
    (hSecure : ∀ (code : CryptoOracle.Interactive.Code) (r : Profile P State),
      r.ExecutesWithin F code → Negligible (fun n =>
        probabilityGap (eventProb (r.logicalGame F code n false) (· = true))
          (eventProb (r.logicalGame F code n true) (· = true)))) :
    (registration (State := State) modelGame hAdvantage).object.Secure F := by
  apply ObservedExecution.secure_of_native
  intro code r hExec
  have h := hSecure code r hExec
  change Negligible (fun n =>
    probabilityGap (eventProb (r.nativeGame F code n false) (· = true))
      (eventProb (r.nativeGame F code n true) (· = true)))
  simpa only [r.nativeGame_eq F code hExec] using h

end CryptoLogic.General.OneUseObservedBackend
