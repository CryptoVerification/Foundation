import Foundation.Crypto.Logic.General.ObservedExecution
import Foundation.Crypto.Logic.General.Backends
import Foundation.Crypto.Semantics.Oracle.OneUseProgramObservation

/-! An arbitrary finite native handler and certified finite caller register
through the same observed-game interface. No XOR semantics or caller query
clock is assumed here. Consumer contracts must establish actual machine laws,
terminal exits and budgets. Observations are mathematical projections. -/
namespace CryptoLogic.General.OneUseContractObservedBackend
open Foundation.Probability Foundation.Symmetric CryptoOracle.Interactive
universe u v
set_option backward.isDefEq.respectTransparency false

structure Profile (P : CryptoGoal.{u}) (State : Type v) where
  width : Nat → Nat
  oracle : ∀ n, P.Instance n → Bool → BitOracle State
  caller : ∀ n, P.Instance n → Bool → Configuration State
  cap : Nat → Nat
  horizon : Nat → Nat
  readPhysical : ∀ n, P.Instance n → Bool → OneUseInitialization.Control State → Bool
  keyGame : CryptoOracle.Interactive.Code → ∀ n, P.Instance n → Bool → Bits (width n) → PMF Bool

namespace Profile
variable {P : CryptoGoal.{u}} {State : Type v} (r : Profile P State)

def ExecutesWithin (native : Machine.Program) (F : InstanceFamily P)
    (code : CryptoOracle.Interactive.Code) : Prop :=
  PolynomiallyBounded r.horizon ∧ ∀ n side,
    (6 * r.width n + 5 + r.cap n ≤ r.horizon n) ∧
    ∃ consumers : ∀ key : Bits (r.width n),
      OneUseProgramContract.Consumer native code (r.oracle n (F n) side)
        (r.caller n (F n) side) (OneUseProgramInitialization.store key),
      (∀ key, (consumers key).execution.budget () ≤ r.cap n) ∧
      (∀ key, ((consumers key).execution.semantics ()).map
        (r.readPhysical n (F n) side ∘ OneUseInitialization.Control.active) =
          r.keyGame code n (F n) side key)

noncomputable def nativeGame (native : Machine.Program) (F : InstanceFamily P)
    (code : CryptoOracle.Interactive.Code) (n : Nat) (side : Bool) : PMF Bool :=
  (TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen
    native code (r.oracle n (F n) side) (r.caller n (F n) side))
    (r.horizon n) (.initializing (.generating
      (Machine.Configuration.initial (List.replicate (r.width n) true))))).map (r.readPhysical n (F n) side)

noncomputable def logicalGame (F : InstanceFamily P) (code : CryptoOracle.Interactive.Code)
    (n : Nat) (side : Bool) : PMF Bool :=
  (uniform (Bits (r.width n))).bind (r.keyGame code n (F n) side)

theorem nativeGame_eq (native : Machine.Program) (F : InstanceFamily P)
    (code : CryptoOracle.Interactive.Code) (hExec : r.ExecutesWithin native F code) (n : Nat) (side : Bool) :
    r.nativeGame native F code n side = r.logicalGame F code n side := by
  obtain ⟨hHorizon, consumers, hCap, hGame⟩ := hExec.2 n side
  exact OneUseProgramInitialization.observed_run native code (r.oracle n (F n) side)
    (r.caller n (F n) side) (r.width n) consumers (r.cap n) hCap
    (r.readPhysical n (F n) side) (r.keyGame code n (F n) side) hGame (r.horizon n) hHorizon

end Profile

variable {P : CryptoGoal.{u}} {State : Type v}

noncomputable def registration (native : Machine.Program)
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true))) :
    ObservedExecution Backends.system .interactive P where
  Resources := Profile P State
  ExecutesWithin := fun F code r => r.ExecutesWithin native F code
  game := fun F code r => r.nativeGame native F code
  modelGame := modelGame
  advantage_eq := hAdvantage

def witness (native : Machine.Program)
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))
    (F A) (code : CryptoOracle.Interactive.Code) (r : Profile P State)
    (hExec : r.ExecutesWithin native F code)
    (hLogical : ∀ n side, r.logicalGame F code n side = modelGame F A n side) :
    (registration (State := State) native modelGame hAdvantage).object.Witness F A := by
  have hReal : (registration (State := State) native modelGame hAdvantage).Realizes F A code r := by
    intro n side
    exact (r.nativeGame_eq native F code hExec n side).trans (hLogical n side)
  exact ⟨code, r, hExec, hReal, ⟨code, r, hExec, hReal⟩⟩

theorem secure_of_logical (native : Machine.Program)
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))
    (F : InstanceFamily P)
    (hSecure : ∀ (code : CryptoOracle.Interactive.Code) (r : Profile P State),
      r.ExecutesWithin native F code → Negligible (fun n =>
        probabilityGap (eventProb (r.logicalGame F code n false) (· = true))
          (eventProb (r.logicalGame F code n true) (· = true)))) :
    (registration (State := State) native modelGame hAdvantage).object.Secure F := by
  apply ObservedExecution.secure_of_native
  intro code r hExec
  have h := hSecure code r hExec
  change Negligible (fun n =>
    probabilityGap (eventProb (r.nativeGame native F code n false) (· = true))
      (eventProb (r.nativeGame native F code n true) (· = true)))
  simpa only [r.nativeGame_eq native F code hExec] using h

end CryptoLogic.General.OneUseContractObservedBackend
