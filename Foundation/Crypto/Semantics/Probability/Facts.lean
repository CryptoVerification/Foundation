import Foundation.Crypto.Semantics.Probability.Comp

/-! Distribution facts independent of a scheme, tag representation or machine.
Semantic maps do not assert any runtime cost for their host functions. -/
namespace Foundation.Probability
open scoped ENNReal

theorem uniform_map_equiv {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    (uniform α).map e = uniform β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [uniform, Fintype.card_congr e]
  · intro a ha
    simp only [ite_eq_right_iff]
    intro h
    exact False.elim (ha (by simpa using congrArg e.symm h.symm))

theorem uniform_pair {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (uniform α).bind (fun a => (uniform β).map (fun b => (a, b))) = uniform (α × β) := by
  classical
  ext ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, uniform, ENNReal.mul_inv,
    Prod.mk.injEq, ite_and, mul_ite]

theorem uniform_guess {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    eventProb (uniform α) (· = a) = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  simp [eventProb, uniform, Set.indicator_apply]

/-- Equality of continuations is required only on reachable branches. -/
theorem bind_congr_of_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff _ _).mpr ha)]

/-- A supported branch of an exact mixture has a matching supported
observation in the target law. This transfers state predicates, not branch
probabilities; the observation may deliberately forget a transcript. -/
theorem support_witness_of_mixture_map_eq {Index Source Target Observation : Type*}
    (mixture : PMF Index) (branches : Index → PMF Source) (target : PMF Target)
    (observeSource : Source → Observation) (observeTarget : Target → Observation)
    (same : mixture.bind (fun index => (branches index).map observeSource) = target.map observeTarget)
    (index : Index) (selected : index ∈ mixture.support) (source : Source)
    (reachable : source ∈ (branches index).support) :
    ∃ result ∈ target.support, observeTarget result = observeSource source := by
  have member : observeSource source ∈
      (mixture.bind (fun index => (branches index).map observeSource)).support := by
    rw [PMF.mem_support_bind_iff]
    refine ⟨index, selected, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨source, reachable, rfl⟩
  rw [same, PMF.mem_support_map_iff] at member
  exact member

theorem eventProb_le_one {α : Type*} (p : PMF α) (event : α → Prop) :
    eventProb p event ≤ 1 := by
  unfold eventProb
  calc
    _ ≤ p.toOuterMeasure Set.univ := MeasureTheory.OuterMeasure.mono _ (Set.subset_univ _)
    _ = 1 := by rw [PMF.toOuterMeasure_apply]; simp

theorem eventProb_mono {α : Type*} (p : PMF α) {event other : α → Prop}
    (h : ∀ a, event a → other a) : eventProb p event ≤ eventProb p other :=
  MeasureTheory.OuterMeasure.mono _ h

/-- Event implication is needed only for outcomes having nonzero mass. -/
theorem eventProb_mono_of_support {α : Type*} (p : PMF α) {event other : α → Prop}
    (h : ∀ a ∈ p.support, event a → other a) : eventProb p event ≤ eventProb p other := by
  classical
  unfold eventProb
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases hz : p a = 0
  · simp [Set.indicator_apply, hz]
  · by_cases he : event a
    · have ho := h a ((PMF.mem_support_iff _ _).mpr hz) he
      simp [he, ho]
    · simp [Set.indicator_apply, he]

theorem eventProb_congr_of_support {α : Type*} (p : PMF α) {event other : α → Prop}
    (h : ∀ a ∈ p.support, event a ↔ other a) : eventProb p event = eventProb p other :=
  le_antisymm (eventProb_mono_of_support p (fun a ha => (h a ha).mp))
    (eventProb_mono_of_support p (fun a ha => (h a ha).mpr))

theorem eventProb_or_le {α : Type*} (p : PMF α) (left right : α → Prop) :
    eventProb p (fun a => left a ∨ right a) ≤ eventProb p left + eventProb p right := by
  exact MeasureTheory.measure_union_le (μ := p.toOuterMeasure) {a | left a} {a | right a}

theorem eventProb_map {α β : Type*} (p : PMF α) (f : α → β) (event : β → Prop) :
    eventProb (p.map f) event = eventProb p (fun a => event (f a)) := by
  unfold eventProb
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- A list of possible guesses may contain duplicates; no disjointness or
independence assumption is needed for this union bound. -/
theorem uniform_mem_list {α : Type*} [Fintype α] [Nonempty α] (values : List α) :
    eventProb (uniform α) (fun value => value ∈ values) ≤
      values.length * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  induction values with
  | nil => simp [eventProb]
  | cons head tail ih =>
      calc
        _ ≤ eventProb (uniform α) (· = head) +
            eventProb (uniform α) (fun value => value ∈ tail) := by
          simpa only [List.mem_cons] using eventProb_or_le (uniform α) (· = head) (· ∈ tail)
        _ ≤ (Fintype.card α : ℝ≥0∞)⁻¹ +
            tail.length * (Fintype.card α : ℝ≥0∞)⁻¹ := by
          rw [uniform_guess]
          exact add_le_add (le_refl _) ih
        _ = _ := by simp [Nat.cast_add, add_mul, add_comm]

/-- Exact decomposition of an event probability over a shared random branch. -/
theorem eventProb_bind_eq {A B : Type} (law : ProbComp A) (next : A → ProbComp B)
    (event : B → Prop) :
    eventProb (law.bind next) event = ∑' a, law a * eventProb (next a) event := by
  unfold eventProb
  rw [PMF.toOuterMeasure_bind_apply]

/-- A continuation bound may fail on a bad event. The final error increases
by at most that event's probability, with no factor of two. -/
theorem eventProb_bind_le_bad_add {α β : Type*} (p : PMF α) (f : α → PMF β)
    (bad : α → Prop) (event : β → Prop) (bound : ℝ≥0∞)
    (h : ∀ a ∈ p.support, ¬bad a → eventProb (f a) event ≤ bound) :
    eventProb (p.bind f) event ≤ eventProb p bad + bound := by
  classical
  unfold eventProb
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' a, ((if bad a then p a else 0) + p a * bound) := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases hz : p a = 0
      · simp [hz]
      by_cases hb : bad a
      · simp only [hb, ↓reduceIte]
        calc
          _ ≤ p a * 1 := mul_le_mul' (le_refl _) (eventProb_le_one (f a) event)
          _ ≤ p a + p a * bound := by simp
      · simp only [hb, ↓reduceIte, zero_add]
        exact mul_le_mul' (le_refl _) (h a ((PMF.mem_support_iff _ _).mpr hz) hb)
    _ = _ := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul,
        PMF.toOuterMeasure_apply]
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- A bound need only hold on branches that have nonzero probability. -/
theorem eventProb_bind_le_of_support {α β : Type*} (p : PMF α) (f : α → PMF β)
    (event : β → Prop) (bound : ℝ≥0∞)
    (h : ∀ a ∈ p.support, eventProb (f a) event ≤ bound) :
    eventProb (p.bind f) event ≤ bound := by
  unfold eventProb
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' a, p a * bound := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : p a = 0
      · simp [ha]
      · exact mul_le_mul_right (h a ((PMF.mem_support_iff _ _).mpr ha)) (p a)
    _ = bound := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem eventProb_bind_le {α β : Type*} (p : PMF α) (f : α → PMF β)
    (event : β → Prop) (bound : ℝ≥0∞)
    (h : ∀ a, eventProb (f a) event ≤ bound) :
    eventProb (p.bind f) event ≤ bound :=
  eventProb_bind_le_of_support p f event bound (fun a _ => h a)

end Foundation.Probability
