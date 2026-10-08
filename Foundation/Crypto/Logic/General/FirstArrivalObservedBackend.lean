import Foundation.Crypto.Logic.General.ObservedExecution
import Foundation.Crypto.Semantics.BoundaryStability

/-! Machine-independent registration with actual first-terminal time.
The supplied joint law must equal the stopped physical execution and all
its branches must terminate. Peak bounds refer to the same unstopped step
relation, initial state, finite code and analysis horizon. -/
namespace CryptoLogic.General.FirstArrivalObservedBackend
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

set_option linter.checkUnivs false in
structure Runtime (K : CodeSystem) (m : K.Machine) where
  Context : Type v
  State : Type w
  step : K.Code m → Context → State → PMF State
  initial : K.Code m → Context → State
  terminal : K.Code m → Context → State → Bool
  absorb : ∀ code context state, terminal code context state = true →
    step code context state = PMF.pure state
  observe : K.Code m → Context → State × Nat → Bool

structure Profile {K : CodeSystem} {m : K.Machine} (P : CryptoGoal.{u}) (R : Runtime.{v,w} K m) where
  context : ∀ n, P.Instance n → Bool → R.Context
  horizon : Nat → Nat
  jointLaw : K.Code m → ∀ n, P.Instance n → Bool → PMF (R.State × Nat)

namespace Profile
variable {K : CodeSystem} {m : K.Machine} {P : CryptoGoal.{u}}
    (R : Runtime.{v,w} K m) (r : Profile P R)

def ExecutesWithin (F : InstanceFamily P) (code : K.Code m) : Prop :=
  PolynomiallyBounded r.horizon ∧ ∀ n side,
    runToBoundary (R.step code (r.context n (F n) side))
      (R.terminal code (r.context n (F n) side)) (r.horizon n)
      (R.initial code (r.context n (F n) side)) = r.jointLaw code n (F n) side ∧
    ∀ result ∈ (r.jointLaw code n (F n) side).support,
      R.terminal code (r.context n (F n) side) result.1 = true

noncomputable def logicalGame (code : K.Code m) (n : Nat) (instanceValue : P.Instance n) (side : Bool) : PMF Bool :=
  (r.jointLaw code n instanceValue side).map (R.observe code (r.context n instanceValue side))

noncomputable def nativeGame (F : InstanceFamily P) (code : K.Code m) (n : Nat) (side : Bool) : PMF Bool :=
  (runToBoundary (R.step code (r.context n (F n) side))
    (R.terminal code (r.context n (F n) side)) (r.horizon n)
    (R.initial code (r.context n (F n) side))).map (R.observe code (r.context n (F n) side))

theorem nativeGame_eq (F : InstanceFamily P) (code : K.Code m)
    (hExec : r.ExecutesWithin R F code) (n : Nat) (side : Bool) :
    r.nativeGame R F code n side = r.logicalGame R code n (F n) side := by
  rw [nativeGame, (hExec.2 n side).1]
  rfl

/-- Increasing analysis fuel cannot turn padded time into observed time. -/
theorem jointLaw_of_le (F : InstanceFamily P) (code : K.Code m)
    (hExec : r.ExecutesWithin R F code) (n : Nat) (side : Bool) (fuel : Nat)
    (hFuel : r.horizon n ≤ fuel) :
    runToBoundary (R.step code (r.context n (F n) side))
      (R.terminal code (r.context n (F n) side)) fuel (R.initial code (r.context n (F n) side)) =
      r.jointLaw code n (F n) side := by
  rw [runToBoundary_fuel_stable _ _ (r.horizon n) fuel _ hFuel ?_, (hExec.2 n side).1]
  intro result hr
  rw [(hExec.2 n side).1] at hr
  exact (hExec.2 n side).2 result hr

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
    (hLogical : ∀ n side, r.logicalGame R code n (F n) side = modelGame F A n side) :
    (registration R modelGame hAdvantage).object.Witness F A := by
  have hReal : (registration R modelGame hAdvantage).Realizes F A code r := by
    intro n side
    exact (r.nativeGame_eq R F code hExec n side).trans (hLogical n side)
  exact ⟨code, r, hExec, hReal, ⟨code, r, hExec, hReal⟩⟩

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
    (hLogical : ∀ n side, r.logicalGame R code n (F n) side = modelGame F A n side) :
    (peakRegistration R modelGame hAdvantage measure).object.Witness F A := by
  have hReal : (peakRegistration R modelGame hAdvantage measure).Realizes F A code (r, cap) := by
    intro n side
    exact (r.nativeGame_eq R F code hExec n side).trans (hLogical n side)
  exact ⟨code, (r, cap), ⟨hExec, hPeak⟩, hReal, ⟨code, (r, cap), ⟨hExec, hPeak⟩, hReal⟩⟩

def forgetPeak (measure : K.Code m → R.Context → R.State → Nat) (F A)
    (W : (peakRegistration R modelGame hAdvantage measure).object.Witness F A) :
    (registration R modelGame hAdvantage).object.Witness F A :=
  ⟨W.code, W.resources.1, W.executes.1, W.realizes,
    ⟨W.code, W.resources.1, W.executes.1, W.realizes⟩⟩

theorem forgetPeak_code (measure : K.Code m → R.Context → R.State → Nat) (F A)
    (W : (peakRegistration R modelGame hAdvantage measure).object.Witness F A) :
    (forgetPeak R modelGame hAdvantage measure F A W).code = W.code := rfl

theorem secure_of_logical (F : InstanceFamily P)
    (hSecure : ∀ code (r : Profile P R), r.ExecutesWithin R F code →
      Negligible (fun n => probabilityGap
        (eventProb (r.logicalGame R code n (F n) false) (· = true))
        (eventProb (r.logicalGame R code n (F n) true) (· = true)))) :
    (registration R modelGame hAdvantage).object.Secure F := by
  apply ObservedExecution.secure_of_native
  intro code r hExec
  have h := hSecure code r hExec
  change Negligible (fun n => probabilityGap
    (eventProb (r.nativeGame R F code n false) (· = true))
    (eventProb (r.nativeGame R F code n true) (· = true)))
  simpa only [r.nativeGame_eq R F code hExec] using h

theorem peak_secure_of_logical (measure : K.Code m → R.Context → R.State → Nat)
    (F : InstanceFamily P)
    (hSecure : ∀ code (r : Profile P R) cap, r.ExecutesWithin R F code →
      r.WithinPeak R measure cap F code → Negligible (fun n => probabilityGap
        (eventProb (r.logicalGame R code n (F n) false) (· = true))
        (eventProb (r.logicalGame R code n (F n) true) (· = true)))) :
    (peakRegistration R modelGame hAdvantage measure).object.Secure F := by
  apply ObservedExecution.secure_of_native
  intro code r hExec
  have h := hSecure code r.1 r.2 hExec.1 hExec.2
  change Negligible (fun n => probabilityGap
    (eventProb (r.1.nativeGame R F code n false) (· = true))
    (eventProb (r.1.nativeGame R F code n true) (· = true)))
  simpa only [r.1.nativeGame_eq R F code hExec.1] using h

end CryptoLogic.General.FirstArrivalObservedBackend
