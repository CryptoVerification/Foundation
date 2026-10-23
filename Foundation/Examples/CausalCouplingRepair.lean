import Foundation.Examples.SelectedCouplingRepair
import Foundation.Crypto.Semantics.Probability.Facts

/-! A timing-of-information separation for selected correspondence repairs.
A single triangle has two possible future cost profiles. A repair chosen
before the profile cannot attain each profile's pointwise optimum. Ordinary
and diagram methods are subject to the same information restriction. -/
namespace Foundation.Probability.SelectedCouplingGraph.CausalRepair
open Graph
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev Vertex := Fan.Vertex 1
abbrev Edge := Fan.Edge 1

def weights (expensive : Nat) (observed : Bool) : Edge → Nat
  | none => 0
  | some (_, side) => if side = observed then 1 else expensive

/-- A normalized separating cut: root false, tip true, and one middle bit. -/
def cut (choice : Bool) : Vertex → Bool
  | .inl _ => choice
  | .inr side => side

def price (expensive : Nat) (observed choice : Bool) : Nat :=
  if Bool.xor choice observed then 1 else expensive

theorem cut_separates (choice : Bool) :
    cut choice ((Fan.graph 1).source none) ≠ cut choice ((Fan.graph 1).target none) := by
  change false ≠ true
  decide

/-- Every separating cut, even unnormalized, has one of these two prices. -/
theorem cut_price (expensive : Nat) (observed : Bool) (candidate : Vertex → Bool)
    (separated : candidate (.inr false) ≠ candidate (.inr true)) :
    (Fan.graph 1).cutCost (weights expensive observed) candidate =
      price expensive observed (Bool.xor (candidate (.inr false)) (candidate (.inl 0))) := by
  simp only [Graph.cutCost, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
  simp only [weights, Fan.graph, ite_self, Nat.zero_add]
  cases root : candidate (.inr false) <;> cases middle : candidate (.inl 0) <;>
    cases tip : candidate (.inr true) <;> cases observed <;>
    simp_all [price]

theorem normalized_price (expensive : Nat) (observed choice : Bool) :
    (Fan.graph 1).cutCost (weights expensive observed) (cut choice) = price expensive observed choice := by
  simpa only [cut, Bool.false_xor] using cut_price expensive observed (cut choice) (cut_separates choice)

/-- Observing the profile first attains one unit in both futures. -/
theorem after_observation_cost (expensive : Nat) (observed : Bool) :
    (Fan.graph 1).cutCost (weights expensive observed) (cut (!observed)) = 1 := by
  rw [normalized_price]
  cases observed <;> rfl

theorem price_lower (expensive : Nat) (positive : 1 ≤ expensive) (observed choice : Bool) :
    1 ≤ price expensive observed choice := by
  unfold price
  split <;> omega

theorem pointwise_optimal (expensive : Nat) (positive : 1 ≤ expensive) (observed : Bool)
    (candidate : Vertex → Bool) (separated : candidate (.inr false) ≠ candidate (.inr true)) :
    (Fan.graph 1).cutCost (weights expensive observed) (cut (!observed)) ≤
      (Fan.graph 1).cutCost (weights expensive observed) candidate := by
  rw [after_observation_cost, cut_price expensive observed candidate separated]
  exact price_lower expensive positive _ _

/-- One fixed cut encounters the expensive profile in at least one future. -/
theorem before_observation_worst (expensive : Nat) (candidate : Vertex → Bool)
    (separated : candidate (.inr false) ≠ candidate (.inr true)) :
    ∃ observed, (Fan.graph 1).cutCost (weights expensive observed) candidate = expensive := by
  refine ⟨Bool.xor (candidate (.inr false)) (candidate (.inl 0)), ?_⟩
  rw [cut_price expensive _ candidate separated]
  simp [price]

noncomputable def independentPrice (expensive : Nat) (choices : PMF Bool) : PMF Nat :=
  choices.bind fun choice => (uniform Bool).map fun observed => price expensive observed choice

noncomputable def priceLaw (expensive : Nat) : PMF Nat :=
  (uniform Bool).map fun bit => if bit then 1 else expensive

theorem fixed_price_law (expensive : Nat) (choice : Bool) :
    (uniform Bool).map (fun observed => price expensive observed choice) = priceLaw expensive := by
  have law := congrArg (fun p => p.map (fun bit => if bit then 1 else expensive))
    (uniform_map_equiv (xorEquiv choice))
  simpa only [PMF.map_comp, Function.comp_def, xorEquiv, Equiv.coe_fn_mk, price, priceLaw] using law

/-- Private randomization before the independent future profile does not
improve the cost law: one and expensive each occur with half the mass. -/
theorem independent_price_law (expensive : Nat) (choices : PMF Bool) :
    independentPrice expensive choices = priceLaw expensive := by
  simp only [independentPrice, fixed_price_law, PMF.bind_const]

noncomputable def beforePrice (expensive : Nat) (certificates : PMF (Vertex → Bool)) : PMF Nat :=
  certificates.bind fun candidate => (uniform Bool).map fun observed =>
    (Fan.graph 1).cutCost (weights expensive observed) candidate

/-- This includes arbitrary distributions on all separating cuts, without
assuming a particular orientation or a two-choice implementation. -/
theorem before_price_law (expensive : Nat) (certificates : PMF (Vertex → Bool))
    (valid : ∀ candidate ∈ certificates.support, candidate (.inr false) ≠ candidate (.inr true)) :
    beforePrice expensive certificates = priceLaw expensive := by
  unfold beforePrice
  calc
    _ = certificates.bind (fun _ => priceLaw expensive) := by
      apply bind_congr_of_support
      intro candidate supported
      simp_rw [cut_price expensive _ candidate (valid candidate supported)]
      exact fixed_price_law expensive _
    _ = _ := PMF.bind_const _ _

noncomputable def afterPrice (expensive : Nat) : PMF Nat :=
  (uniform Bool).map fun observed => price expensive observed (!observed)

theorem after_price_law (expensive : Nat) : afterPrice expensive = PMF.pure 1 := by
  have constant : (fun observed => price expensive observed (!observed)) = fun _ => (1 : Nat) := by
    funext observed
    cases observed <;> rfl
  unfold afterPrice
  rw [constant]
  exact PMF.map_const _ _

theorem expensive_probability (expensive : Nat) (different : expensive ≠ 1) (choices : PMF Bool) :
    eventProb (independentPrice expensive choices) (· = expensive) = (2 : ℝ≥0∞)⁻¹ := by
  rw [independent_price_law, priceLaw, eventProb_map]
  have predicate : (fun bit : Bool => (if bit then 1 else expensive) = expensive) = (fun bit => bit = false) := by
    funext bit
    cases bit <;> simp [Ne.symm different]
  rw [predicate]
  simpa using uniform_guess false

/-- The discrepancy survives arbitrary private randomized choices made
before the profile. It is not a consequence of forbidding randomization. -/
theorem causal_gap (expensive : Nat) (different : expensive ≠ 1) (choices : PMF Bool) :
    independentPrice expensive choices ≠ afterPrice expensive := by
  intro same
  have probability := expensive_probability expensive different choices
  rw [same, after_price_law] at probability
  simp [eventProb, Ne.symm different] at probability
  have nonzero : (2 : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by norm_num)
  exact nonzero probability.symm

/-- Pointwise feasible optimal repairs need not assemble into one randomized
choice made before future information is available. Both quantifiers are
explicit; this is not a comparison of two proof systems. -/
theorem pointwise_not_precommitted (expensive : Nat) (strict : 1 < expensive) :
    (∀ observed, ∃ candidate : Vertex → Bool,
      candidate (.inr false) ≠ candidate (.inr true) ∧
      (Fan.graph 1).cutCost (weights expensive observed) candidate = 1) ∧
    (∀ certificates : PMF (Vertex → Bool),
      (∀ candidate ∈ certificates.support, candidate (.inr false) ≠ candidate (.inr true)) →
      beforePrice expensive certificates ≠ PMF.pure 1) := by
  refine ⟨?_, ?_⟩
  · intro observed
    exact ⟨cut (!observed), cut_separates _, after_observation_cost _ _⟩
  · intro certificates valid
    rw [before_price_law expensive certificates valid]
    have gap := causal_gap expensive (Nat.ne_of_gt strict) (PMF.pure false)
    rwa [independent_price_law, after_price_law] at gap

end Foundation.Probability.SelectedCouplingGraph.CausalRepair
