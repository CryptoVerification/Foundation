import Foundation.Crypto.Logic.Polygraph.GameProofJointEventBudget
import Foundation.Constructions.Symmetric.RandomFunctionMACProofEdits

/-! Simultaneous views of ONE complete adaptive random-function MAC run.
The comparison keeps the table, signing history and public trace; only the
acceptance bit is cleared in the ideal view. All views share that one bit.
The improvement is over occurrence-additive union accounting, not over all
ordinary proofs, and it is not a bound for independent forgery attempts. -/
namespace Foundation.Examples.RandomFunctionMACSharedEventBudget
open Foundation.Probability CryptoOracle
open Foundation.Symmetric.RandomFunctionMACProofEdits
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open JointEventBudget
open scoped ENNReal BigOperators
variable {Input Tag : Type}
set_option backward.isDefEq.respectTransparency false

abbrev Transcript (Input Tag : Type) := Outcome Input Tag (Bool × List Input) (RandomOracle.Table Input Tag)

def erase (out : Transcript Input Tag) : Transcript Input Tag :=
  { out with result := (false, out.result.2) }

theorem erase_eq (out : Transcript Input Tag) (good : out.result.1 ≠ true) : erase out = out := by
  rcases out with ⟨⟨accepted, signed⟩, state, trace⟩
  cases accepted <;> simp_all [erase]

theorem different_iff (out : Transcript Input Tag) : out ≠ erase out ↔ out.result.1 = true := by
  rcases out with ⟨⟨accepted, signed⟩, state, trace⟩
  cases accepted <;> simp [erase]

def layout (n : Nat) : Layout (Fin n × Bool) (Fin n) Unit Unit where
  source := fun index => (index, false)
  target := fun index => (index, true)
  needs := fun _ => ∅
  charges := fun _ => {()}

def model (n : Nat) : Realization (layout n) (Transcript Input Tag) (Fin n × Transcript Input Tag) where
  value := fun vertex out => (vertex.1, if vertex.2 then erase out else out)
  bad := fun _ out => out.result.1 = true
  root := by
    intro index out good
    change (index, out) = (index, erase out)
    rw [erase_eq out (good () (by simp [layout]))]

def requests (n : Nat) (index : Fin n) : Request (layout n) :=
  ⟨(index, false), (index, true), .atom index⟩

theorem support_singleton (n : Nat) (positive : 0 < n) : support (requests n) = {()} := by
  classical
  ext label
  constructor
  · intro _; exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  · intro _
    exact Finset.mem_biUnion.mpr ⟨⟨0, positive⟩, Finset.mem_univ _, by simp [requests, Plan.charges, layout]⟩

theorem failure_iff (n : Nat) (positive : 0 < n) (out : Transcript Input Tag) :
    failure (model (Input := Input) (Tag := Tag) n) (requests n) out ↔ out.result.1 = true := by
  constructor
  · rintro ⟨index, different⟩
    apply (different_iff out).mp
    intro equal
    apply different
    exact congrArg (fun value => (index, value)) equal
  · intro accepted
    refine ⟨⟨0, positive⟩, ?_⟩
    intro equal
    exact (different_iff out).mpr accepted (congrArg Prod.snd equal)

variable [DecidableEq Input] [DecidableEq Tag]

noncomputable def law [Fintype Tag] [Nonempty Tag] (attack : Program Input Tag (Input × Tag)) :
    ProbComp (Transcript Input Tag) := (before attack).run RandomOracle.oracle [] []

theorem simultaneous_bound [Fintype Tag] [Nonempty Tag] (n : Nat) (positive : 0 < n)
    (attack : Program Input Tag (Input × Tag)) :
    eventProb (law attack) (failure (model n) (requests n)) ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  have localBound : ∀ charge ∈ support (requests n),
      eventProb (law attack) ((model (Input := Input) (Tag := Tag) n).bad charge) ≤
        (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
    intro _ _
    exact before_bound attack [] [] (by intro entry member; cases member)
  have bound := family_bound (model n) (requests n) (law attack) (fun _ => (Fintype.card Tag : ℝ≥0∞)⁻¹) localBound
  rw [support_singleton n positive] at bound
  simpa only [SharedEventBudget.budget, Finset.sum_singleton] using bound

/-- A valid, conventional per-view union bound on the very same joint law.
The one local MAC bound may be shared in both derivations. -/
theorem occurrence_bound [Fintype Tag] [Nonempty Tag] (n : Nat)
    (attack : Program Input Tag (Input × Tag)) :
    eventProb (law attack) (failure (model n) (requests n)) ≤ n * (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  classical
  let perView := fun index out => (model (Input := Input) (Tag := Tag) n).value (requests n index).source out ≠
    (model n).value (requests n index).target out
  have localBound (index : Fin n) : eventProb (law attack) (perView index) ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
    apply (eventProb_mono (law attack) (fun out different => (different_iff out).mp (by
      intro equal; exact different (congrArg (fun value => (index, value)) equal)))).trans
    exact before_bound attack [] [] (by intro entry member; cases member)
  have bound := SharedEventBudget.covers (law attack) perView Finset.univ (failure (model n) (requests n))
    (fun _ failed => by obtain ⟨index, different⟩ := failed; exact ⟨index, Finset.mem_univ _, different⟩)
    (fun _ => (Fintype.card Tag : ℝ≥0∞)⁻¹) (fun index _ => localBound index)
  simpa [SharedEventBudget.budget, nsmul_eq_mul] using bound

theorem byte_bound (n : Nat) (positive : 0 < n)
    (attack : Program (Fin 8) (Fin 256) (Fin 8 × Fin 256)) :
    eventProb (law attack) (failure (model n) (requests n)) ≤ (256 : ℝ≥0∞)⁻¹ := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using simultaneous_bound n positive attack

theorem strict_budget_improvement (n : Nat) (many : 1 < n) :
    SharedEventBudget.budget (fun _ : Unit => (256 : ℝ≥0∞)⁻¹) ({()} : Finset Unit) <
      ∑ _index : Fin n, (256 : ℝ≥0∞)⁻¹ := by
  simpa [SharedEventBudget.budget, nsmul_eq_mul] using SharedEventBudget.byte_strict n many

theorem displayed_256_views :
    SharedEventBudget.budget (fun _ : Unit => (256 : ℝ≥0∞)⁻¹) ({()} : Finset Unit) = (256 : ℝ≥0∞)⁻¹ ∧
    (∑ _index : Fin 256, (256 : ℝ≥0∞)⁻¹) = 1 := by
  constructor
  · simp [SharedEventBudget.budget]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

end Foundation.Examples.RandomFunctionMACSharedEventBudget
