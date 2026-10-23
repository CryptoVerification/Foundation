import Foundation.Crypto.Meta.Polygraph.InformationScheduleCertificate
import Foundation.Examples.InformationScheduleBaseline
import Foundation.Examples.CausalCouplingRepair

/-! Dependency-sensitive acceptance, ordinary replay comparison, and the same
before/after information cost gap. The checker accepts independent moves and
rejects moving a future-dependent choice before its observation. -/
namespace CryptoOracle.InformationSchedule.Example
open Foundation.Probability
open Foundation.Probability.SelectedCouplingGraph.CausalRepair
set_option backward.isDefEq.respectTransparency false

section Comparison
variable {Variable Key : Type} [DecidableEq Variable] [DecidableEq Key]
variable (signature : Key → Finset Variable)

theorem swap_erases (position : Nat) (word : List (Action Variable Key)) :
    (Certificate.swapAt signature position word).map Sigma.fst = Baseline.swapAt signature position word := by
  induction position generalizing word with
  | zero =>
      cases word with
      | nil => rfl
      | cons first tail =>
          cases tail with
          | nil => rfl
          | cons second rest =>
              by_cases allowed : independent signature first second = true <;>
                simp [Certificate.swapAt, Baseline.swapAt, allowed]
  | succ position ih =>
      cases word with
      | nil => rfl
      | cons first rest =>
          simp only [Certificate.swapAt, Baseline.swapAt, ← ih rest, Option.map_map, Function.comp_def]

theorem replay_erases (positions : List Nat) (word : List (Action Variable Key)) :
    (Certificate.replay signature word positions).map Sigma.fst = Baseline.replay signature word positions := by
  induction positions generalizing word with
  | nil => rfl
  | cons position rest ih =>
      have swap := swap_erases signature position word
      cases middle : Certificate.swapAt signature position word with
      | none =>
          have plain : Baseline.swapAt signature position word = none := by simpa only [middle, Option.map_none] using swap.symm
          simp [Certificate.replay, Baseline.replay, middle, plain]
      | some pair =>
          have plain : Baseline.swapAt signature position word = some pair.1 := by
            simpa only [middle, Option.map_some] using swap.symm
          simp only [Certificate.replay, middle, Option.bind_some, Baseline.replay, plain]
          have next := ih pair.1
          cases last : Certificate.replay signature pair.1 rest with
          | none => simpa [last] using next
          | some final => simpa [last] using next

/-- Exact acceptance equality for ALL scripts, not only displayed examples. -/
theorem validates_eq (seen : Finset Variable) (word target : List (Action Variable Key)) (positions : List Nat) :
    Certificate.validates signature seen word target positions = Baseline.validates signature seen word target positions := by
  have erases := replay_erases signature positions word
  cases result : Certificate.replay signature word positions with
  | none =>
      have plain : Baseline.replay signature word positions = none := by simpa [result] using erases.symm
      simp [Certificate.validates, Certificate.certify, Baseline.validates, result, plain]
  | some pair =>
      have plain : Baseline.replay signature word positions = some pair.1 := by simpa [result] using erases.symm
      by_cases same : pair.1 = target <;>
        simp [Certificate.validates, Certificate.certify, Baseline.validates, result, plain, same]
end Comparison

def signature (key : Bool) : Finset Bool := if key then {false} else ∅

noncomputable def policy : (key : Bool) → ({v // v ∈ signature key} → Bool) → PMF Bool
  | false, _ => PMF.pure false
  | true, inputs => PMF.pure (!(inputs ⟨false, by decide⟩))

def initial (observed : Bool) : State Bool Bool Bool :=
  ⟨fun input => if input then false else observed, ∅, fun _ => none⟩

def independentBefore : List (Action Bool Bool) := [.commit false, .reveal false]
def independentAfter : List (Action Bool Bool) := [.reveal false, .commit false]
def late : List (Action Bool Bool) := [.reveal false, .commit true]
def premature : List (Action Bool Bool) := [.commit true, .reveal false]

theorem accepts_independent : Certificate.validates signature ∅ independentBefore independentAfter [0] = true := by decide_cbv

theorem rejects_premature : Certificate.validates signature ∅ premature late [0] = false := by decide_cbv

theorem rejects_dependency_crossing : Certificate.validates signature ∅ late premature [0] = false := by decide_cbv

theorem no_dependency_cell : ¬ Nonempty (Cell signature late premature) := by
  rintro ⟨cell⟩
  have same := Cell.scan signature cell ∅
  have source : scan signature ∅ late = some {false} := by decide
  have target : scan signature ∅ premature = none := by decide
  rw [source, target] at same
  contradiction

theorem rejects_every_crossing_script (positions : List Nat) :
    Certificate.validates signature ∅ late premature positions = false :=
  Certificate.rejects_invalid_target signature ∅ late premature positions (by decide)

/-- Once the profile is known, an unrelated reveal can still be exchanged. -/
theorem accepts_unrelated :
    Certificate.validates signature {false} [.reveal true, .commit true] [.commit true, .reveal true] [0] = true := by decide_cbv

theorem ordinary_independent (state : State Bool Bool Bool) :
    run signature policy independentBefore state = run signature policy independentAfter state :=
  Baseline.validated_kernel signature policy ∅ independentBefore independentAfter [0]
    (by rw [← validates_eq]; exact accepts_independent) state

def finalPrice (expensive : Nat) (state : State Bool Bool Bool) : Nat :=
  price expensive (state.hidden false) ((state.chosen true).getD false)

noncomputable def scheduleCost (expensive : Nat) (word : List (Action Bool Bool)) : PMF Nat :=
  (uniform Bool).bind fun observed => (run signature policy word (initial observed)).map (finalPrice expensive)

theorem late_cost (expensive : Nat) : scheduleCost expensive late = PMF.pure 1 := by
  have each (observed : Bool) : (run signature policy late (initial observed)).map (finalPrice expensive) = PMF.pure 1 := by
    cases observed <;> simp [run, step, late, policy, finalPrice, price, view, initial, reveal, commit, PMF.pure_map]
  simp only [scheduleCost, each, PMF.bind_const]

/-- The raw premature execution cannot see the future; it reads only its
available inputs. Validation rejects using it as a causal exchange. -/
theorem premature_cost (expensive : Nat) : scheduleCost expensive premature = priceLaw expensive := by
  have each (observed : Bool) : (run signature policy premature (initial observed)).map (finalPrice expensive) =
      PMF.pure (price expensive observed true) := by
    cases observed <;> simp [run, step, premature, policy, finalPrice, price, view, initial, reveal, commit, PMF.pure_map]
  simp only [scheduleCost, each]
  change (uniform Bool).map (fun observed => price expensive observed true) = _
  exact fixed_price_law expensive true

/-- Declared dependencies may overapproximate semantic dependencies. A
constant policy can commute even when this conservative checker rejects. -/
theorem overdeclared_exchange (state : State Bool Bool Bool) :
    run signature (fun _ _ => PMF.pure false) late state =
      run signature (fun _ _ => PMF.pure false) premature state := by
  simp only [late, premature, run, step, PMF.pure_bind, PMF.bind_pure, PMF.pure_map]
  rfl

end CryptoOracle.InformationSchedule.Example
