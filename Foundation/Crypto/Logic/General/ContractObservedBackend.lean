import Foundation.Crypto.Logic.General.ObservedExecution
import Foundation.Crypto.Semantics.ProcedureCompletion

/-! Machine-independent registration from genuine completed execution
contracts. The runtime fixes the concrete step relation, initial state,
terminal predicate and observation for the exact finite code. Profiles supply
instance-dependent contexts and real horizons; no cost is invented here. -/
namespace CryptoLogic.General.ContractObservedBackend
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

set_option linter.checkUnivs false in
structure Runtime (K : CodeSystem) (m : K.Machine) where
  Context : Type v
  State : Type w
  step : K.Code m → Context → State → PMF State
  initial : K.Code m → Context → State
  terminal : K.Code m → Context → State → Prop
  absorb : ∀ code context state, terminal code context state →
    step code context state = PMF.pure state
  observe : K.Code m → Context → State → Bool

structure Profile {K : CodeSystem} {m : K.Machine} (P : CryptoGoal.{u}) (R : Runtime.{v,w} K m) where
  context : ∀ n, P.Instance n → Bool → R.Context
  horizon : Nat → Nat
  logicalGame : K.Code m → ∀ n, P.Instance n → Bool → PMF Bool

namespace Profile
variable {K : CodeSystem} {m : K.Machine} {P : CryptoGoal.{u}}
    (R : Runtime.{v,w} K m) (r : Profile P R)

def ExecutesWithin (F : InstanceFamily P) (code : K.Code m) : Prop :=
  PolynomiallyBounded r.horizon ∧ ∀ n side,
    ∃ C : Completion (R.step code (r.context n (F n) side))
      (R.initial code (r.context n (F n) side)) (R.terminal code (r.context n (F n) side)),
      C.execution.budget () ≤ r.horizon n ∧
      (C.execution.semantics ()).map (R.observe code (r.context n (F n) side)) =
        r.logicalGame code n (F n) side

noncomputable def nativeGame (F : InstanceFamily P) (code : K.Code m) (n : Nat) (side : Bool) : PMF Bool :=
  (TimedExecution.eval (R.step code (r.context n (F n) side)) (r.horizon n)
    (R.initial code (r.context n (F n) side))).map (R.observe code (r.context n (F n) side))

theorem nativeGame_eq (F : InstanceFamily P) (code : K.Code m)
    (hExec : r.ExecutesWithin R F code) (n : Nat) (side : Bool) :
    r.nativeGame R F code n side = r.logicalGame code n (F n) side := by
  obtain ⟨C, hBudget, hGame⟩ := hExec.2 n side
  rw [nativeGame, C.final_run (R.absorb code (r.context n (F n) side)) (r.horizon n) hBudget]
  exact hGame

/-- Optional peak bounds cover every actual intermediate configuration,
including the endpoint. The measure can include the complete finite code. -/
def WithinPeak (measure : K.Code m → R.Context → R.State → Nat) (cap : Nat → Nat)
    (F : InstanceFamily P) (code : K.Code m) : Prop :=
  PolynomiallyBounded cap ∧ ∀ n side elapsed, elapsed ≤ r.horizon n →
    ∀ target ∈ (TimedExecution.eval (R.step code (r.context n (F n) side)) elapsed
      (R.initial code (r.context n (F n) side))).support,
      measure code (r.context n (F n) side) target ≤ cap n

end Profile

variable {K : CodeSystem} {m : K.Machine} {P : CryptoGoal.{u}}
    (R : Runtime.{v,w} K m)
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))

noncomputable def registration : ObservedExecution K m P where
  Resources := Profile P R
  ExecutesWithin := fun F code r => r.ExecutesWithin R F code
  game := fun F code r => r.nativeGame R F code
  modelGame := modelGame
  advantage_eq := hAdvantage

def witness (F A) (code : K.Code m) (r : Profile P R)
    (hExec : r.ExecutesWithin R F code)
    (hLogical : ∀ n side, r.logicalGame code n (F n) side = modelGame F A n side) :
    (registration R modelGame hAdvantage).object.Witness F A := by
  have hReal : (registration R modelGame hAdvantage).Realizes F A code r := by
    intro n side
    exact (r.nativeGame_eq R F code hExec n side).trans (hLogical n side)
  exact ⟨code, r, hExec, hReal, ⟨code, r, hExec, hReal⟩⟩

theorem secure_of_logical (F : InstanceFamily P)
    (hSecure : ∀ code (r : Profile P R), r.ExecutesWithin R F code →
      Negligible (fun n => probabilityGap
        (eventProb (r.logicalGame code n (F n) false) (· = true))
        (eventProb (r.logicalGame code n (F n) true) (· = true)))) :
    (registration R modelGame hAdvantage).object.Secure F := by
  apply ObservedExecution.secure_of_native
  intro code r hExec
  have h := hSecure code r hExec
  change Negligible (fun n => probabilityGap
    (eventProb (r.nativeGame R F code n false) (· = true))
    (eventProb (r.nativeGame R F code n true) (· = true)))
  simpa only [r.nativeGame_eq R F code hExec] using h

/-- Register a supplied peak measure alongside the actual stopping proof.
The backend must identify the measure and prove it bounds real states. -/
noncomputable def peakRegistration (measure : K.Code m → R.Context → R.State → Nat) :
    ObservedExecution K m P where
  Resources := Profile P R × (Nat → Nat)
  ExecutesWithin := fun F code r => r.1.ExecutesWithin R F code ∧ r.1.WithinPeak R measure r.2 F code
  game := fun F code r => r.1.nativeGame R F code
  modelGame := modelGame
  advantage_eq := hAdvantage

def peakWitness (measure : K.Code m → R.Context → R.State → Nat)
    (F A) (code : K.Code m) (r : Profile P R) (cap : Nat → Nat)
    (hExec : r.ExecutesWithin R F code) (hPeak : r.WithinPeak R measure cap F code)
    (hLogical : ∀ n side, r.logicalGame code n (F n) side = modelGame F A n side) :
    (peakRegistration R modelGame hAdvantage measure).object.Witness F A := by
  have hReal : (peakRegistration R modelGame hAdvantage measure).Realizes F A code (r, cap) := by
    intro n side
    exact (r.nativeGame_eq R F code hExec n side).trans (hLogical n side)
  exact ⟨code, (r, cap), ⟨hExec, hPeak⟩, hReal, ⟨code, (r, cap), ⟨hExec, hPeak⟩, hReal⟩⟩

/-- Forgetting the extra peak certificate retains the exact finite code,
context, execution horizon and game realization. -/
def forgetPeak (measure : K.Code m → R.Context → R.State → Nat) (F A)
    (W : (peakRegistration R modelGame hAdvantage measure).object.Witness F A) :
    (registration R modelGame hAdvantage).object.Witness F A :=
  ⟨W.code, W.resources.1, W.executes.1, W.realizes,
    ⟨W.code, W.resources.1, W.executes.1, W.realizes⟩⟩

theorem forgetPeak_code (measure : K.Code m → R.Context → R.State → Nat) (F A)
    (W : (peakRegistration R modelGame hAdvantage measure).object.Witness F A) :
    (forgetPeak R modelGame hAdvantage measure F A W).code = W.code := rfl

theorem logical_advantage (F A)
    (W : (registration R modelGame hAdvantage).object.Witness F A) (n : Nat) :
    advantageProfile P F A n = probabilityGap
      (eventProb (W.resources.logicalGame W.code n (F n) false) (· = true))
      (eventProb (W.resources.logicalGame W.code n (F n) true) (· = true)) := by
  have h := ObservedExecution.realizes_advantage (registration R modelGame hAdvantage)
    F A W.code W.resources W.realizes n
  change advantageProfile P F A n = probabilityGap
    (eventProb (W.resources.nativeGame R F W.code n false) (· = true))
    (eventProb (W.resources.nativeGame R F W.code n true) (· = true)) at h
  simpa only [Profile.nativeGame_eq R W.resources F W.code W.executes] using h

theorem peak_secure_of_logical (measure : K.Code m → R.Context → R.State → Nat)
    (F : InstanceFamily P)
    (hSecure : ∀ code (r : Profile P R) cap, r.ExecutesWithin R F code →
      r.WithinPeak R measure cap F code → Negligible (fun n => probabilityGap
        (eventProb (r.logicalGame code n (F n) false) (· = true))
        (eventProb (r.logicalGame code n (F n) true) (· = true)))) :
    (peakRegistration R modelGame hAdvantage measure).object.Secure F := by
  apply ObservedExecution.secure_of_native
  intro code r hExec
  have h := hSecure code r.1 r.2 hExec.1 hExec.2
  change Negligible (fun n => probabilityGap
    (eventProb (r.1.nativeGame R F code n false) (· = true))
    (eventProb (r.1.nativeGame R F code n true) (· = true)))
  simpa only [Profile.nativeGame_eq R r.1 F code hExec.1] using h

end CryptoLogic.General.ContractObservedBackend
