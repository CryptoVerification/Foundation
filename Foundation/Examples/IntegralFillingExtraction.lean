import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Integer filling certificates and an explicit cache-aware trace map.

The fan boundary below is an algebraic cellular boundary model. The proof does
not assume that every successful cryptographic extractor collects every label:
that computational bridge still requires the separate DL reduction.
No claim of novelty or necessity of an infinity-category is made here. -/

namespace Foundation.Examples.IntegralFillingExtraction

open scoped BigOperators

section Certificate

variable {I B : Type*} [Fintype I]

def weightedMass (weight : I → ℕ) (chain : I → ℤ) : ℕ :=
  ∑ i, weight i * (chain i).natAbs

/-- A dual certificate can be checked on the finitely many generators of a
linear boundary map. Its absolute value bounds the cost of every signed chain. -/
theorem calibration_bound (weight : I → ℕ) (load chain : I → ℤ)
    (unitBound : ∀ i, (load i).natAbs ≤ weight i) :
    (∑ i, load i * chain i).natAbs ≤ weightedMass weight chain := by
  calc
    _ ≤ ∑ i, (load i * chain i).natAbs := Int.natAbs_sum_le _ _
    _ = ∑ i, (load i).natAbs * (chain i).natAbs := by
      simp only [Int.natAbs_mul]
    _ ≤ weightedMass weight chain := by
      exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (unitBound i)

/-- Lower bound for all integer fillings, without pretending that all such
fillings are executable. The compatibility equation is the dual certificate. -/
theorem filling_lower_bound (boundary : (I → ℤ) → B) (potential : B → ℤ)
    (weight : I → ℕ) (load : I → ℤ)
    (compatible : ∀ chain, potential (boundary chain) = ∑ i, load i * chain i)
    (unitBound : ∀ i, (load i).natAbs ≤ weight i)
    (chain : I → ℤ) (target : B) (fills : boundary chain = target) :
    (potential target).natAbs ≤ weightedMass weight chain := by
  rw [← fills, compatible]
  exact calibration_bound weight load chain unitBound

end Certificate

section Fan

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Outer edges and radial edges of a cyclic fan. For arbitrary `turn` this
still defines the same algebraic incidence map; a cyclic turn gives a disk. -/
def fanBoundary (turn : Equiv.Perm I) (chain : I → ℤ) : (I → ℤ) × (I → ℤ) :=
  (chain, fun i => chain i - chain (turn.symm i))

def fanTarget (multiplicity : ℤ) : (I → ℤ) × (I → ℤ) :=
  (fun _ => multiplicity, fun _ => 0)

def mass (chain : I → ℤ) : ℕ := ∑ i, (chain i).natAbs

def vertexBoundary (turn : Equiv.Perm I) (chain : (I → ℤ) × (I → ℤ)) :
    (I → ℤ) × ℤ :=
  (fun i => chain.1 (turn.symm i) - chain.1 i + chain.2 i, -∑ i, chain.2 i)

omit [DecidableEq I] in
theorem boundary_squared_zero (turn : Equiv.Perm I) (chain : I → ℤ) :
    vertexBoundary turn (fanBoundary turn chain) = (fun _ => 0, 0) := by
  apply Prod.ext
  · funext i
    dsimp [vertexBoundary, fanBoundary]
    ring
  · simp only [vertexBoundary, fanBoundary, Finset.sum_sub_distrib]
    rw [turn.symm.sum_comp]
    simp

omit [Fintype I] [DecidableEq I] in
theorem fan_filling_unique (turn : Equiv.Perm I) (chain : I → ℤ) (k : ℤ)
    (fills : fanBoundary turn chain = fanTarget k) : chain = fun _ => k := by
  exact congrArg Prod.fst fills

omit [Fintype I] [DecidableEq I] in
theorem constant_fills (turn : Equiv.Perm I) (k : ℤ) :
    fanBoundary turn (fun _ => k) = fanTarget k := by
  simp [fanBoundary, fanTarget]

omit [DecidableEq I] in
/-- Exact integral filling mass; negative coefficients cannot cancel away the
required outer boundary. This applies to every integer, not only 0/1 chains. -/
theorem fan_filling_mass (turn : Equiv.Perm I) (chain : I → ℤ) (k : ℤ)
    (fills : fanBoundary turn chain = fanTarget k) :
    mass chain = Fintype.card I * k.natAbs := by
  rw [fan_filling_unique turn chain k fills]
  simp [mass]

/-- A label is charged once if and only if its accepted response has appeared.
Repeated reads of the same cached response do not create new cells. -/
def traceChain (trace : List I) (i : I) : ℤ := if i ∈ trace.toFinset then 1 else 0

theorem trace_mass (trace : List I) : mass (traceChain trace) = trace.toFinset.card := by
  classical
  calc
    mass (traceChain trace) = ∑ i : I, if i ∈ trace.toFinset then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases seen : i ∈ trace.toFinset <;> simp [traceChain, seen]
    _ = trace.toFinset.card :=
      (Finset.card_eq_sum_ite (Finset.subset_univ trace.toFinset)).symm

theorem trace_mass_le_queries (trace : List I) :
    mass (traceChain trace) ≤ trace.length := by
  rw [trace_mass trace]
  exact List.toFinset_card_le trace

omit [Fintype I] in
theorem cached_read_idempotent (trace : List I) (i : I) (seen : i ∈ trace) :
    traceChain (i :: trace) = traceChain trace := by
  funext j
  simp only [traceChain, List.toFinset_cons]
  have mem : i ∈ trace.toFinset := by simpa using seen
  rw [Finset.insert_eq_of_mem mem]

omit [Fintype I] in
theorem trace_fills_iff (turn : Equiv.Perm I) (trace : List I) :
    fanBoundary turn (traceChain trace) = fanTarget 1 ↔ ∀ i, i ∈ trace := by
  constructor
  · intro fills i
    have one := congrFun (fan_filling_unique turn (traceChain trace) 1 fills) i
    by_contra absent
    simp [traceChain, absent] at one
  · intro allSeen
    have same : traceChain trace = fun _ => (1 : ℤ) := by
      funext i
      simp [traceChain, allSeen i]
    rw [same]
    exact constant_fills turn 1

/-- Concrete execution-to-filling transfer. This is not an assumed per-query
mass bound: the trace map and the cache accounting were defined above. -/
theorem complete_trace_query_lower (turn : Equiv.Perm I) (trace : List I)
    (allSeen : ∀ i, i ∈ trace) : Fintype.card I ≤ trace.length := by
  have fills := (trace_fills_iff turn trace).mpr allSeen
  have exactMass := fan_filling_mass turn (traceChain trace) 1 fills
  have bound := trace_mass_le_queries trace
  simpa using exactMass.symm.trans_le bound

/-- Returning every label once realizes a minimum-mass filling. -/
theorem enumeration_attains (turn : Equiv.Perm I) :
    ∃ trace : List I, trace.length = Fintype.card I ∧
      fanBoundary turn (traceChain trace) = fanTarget 1 := by
  classical
  refine ⟨Finset.univ.toList, ?_, ?_⟩
  · simp
  · apply (trace_fills_iff turn _).mpr
    simp

/-- `none` is a rejected response and still costs one oracle call. -/
def acceptedTrace (events : List (Option I)) : List I := events.filterMap id

theorem complete_events_query_lower (turn : Equiv.Perm I) (events : List (Option I))
    (allSeen : ∀ i, i ∈ acceptedTrace events) : Fintype.card I ≤ events.length := by
  have bound := complete_trace_query_lower turn (acceptedTrace events) allSeen
  exact bound.trans (List.length_filterMap_le _ _)

end Fan

section Probability

variable {Seed I : Type*} [Fintype Seed] [Fintype I] [DecidableEq I]

/-- Exact expectation bound for arbitrary finite rational seed laws. The event
means that all labels have been collected; cryptographic success is different. -/
theorem expected_queries_lower (turn : Equiv.Perm I) (weight : Seed → ℚ)
    (nonnegative : ∀ seed, 0 ≤ weight seed) (trace : Seed → List I) :
    (Fintype.card I : ℚ) *
      (∑ seed, if ∀ i, i ∈ trace seed then weight seed else 0) ≤
      ∑ seed, weight seed * ((trace seed).length : ℚ) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro seed _
  split_ifs with collected
  · have bound : (Fintype.card I : ℚ) ≤ ((trace seed).length : ℚ) := by
      exact_mod_cast complete_trace_query_lower turn (trace seed) collected
    simpa [mul_comm] using mul_le_mul_of_nonneg_left bound (nonnegative seed)
  · simp only [mul_zero]
    exact mul_nonneg (nonnegative seed) (Nat.cast_nonneg _)

theorem expected_events_lower (turn : Equiv.Perm I) (weight : Seed → ℚ)
    (nonnegative : ∀ seed, 0 ≤ weight seed) (events : Seed → List (Option I)) :
    (Fintype.card I : ℚ) *
      (∑ seed, if ∀ i, i ∈ acceptedTrace (events seed) then weight seed else 0) ≤
      ∑ seed, weight seed * ((events seed).length : ℚ) := by
  classical
  refine (expected_queries_lower turn weight nonnegative
    (fun seed => acceptedTrace (events seed))).trans ?_
  apply Finset.sum_le_sum
  intro seed _
  apply mul_le_mul_of_nonneg_left _ (nonnegative seed)
  exact_mod_cast List.length_filterMap_le id (events seed)

end Probability

end Foundation.Examples.IntegralFillingExtraction
