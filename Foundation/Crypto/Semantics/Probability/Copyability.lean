import Foundation.Crypto.Semantics.Probability.Facts

/-! Copying a sampled value is distinct from independently rerunning a kernel.
For discrete PMFs, commuting these operations characterizes point masses.
Discarding below is an output projection of a normalized PMF, not deletion of
live machine state or elimination of a potentially nonterminating computation. -/
namespace Foundation.Probability.Copyability
variable {A B : Type}

noncomputable def shared (law : PMF A) : PMF (A × A) := law.map (fun value => (value, value))
noncomputable def independent (first : PMF A) (second : PMF B) : PMF (A × B) :=
  first.bind (fun x => second.map (fun y => (x, y)))

theorem support_shared (law : PMF A) (x y : A) (member : (x, y) ∈ (shared law).support) : x = y := by
  obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  exact (congrArg Prod.fst same).symm.trans (congrArg Prod.snd same)

theorem support_independent (first : PMF A) (second : PMF B) (x : A) (y : B)
    (one : x ∈ first.support) (two : y ∈ second.support) :
    (x, y) ∈ (independent first second).support := by
  exact (PMF.mem_support_bind_iff _ _ _).mpr
    ⟨x, one, (PMF.mem_support_map_iff _ _ _).mpr ⟨y, two, rfl⟩⟩

theorem shared_pure (value : A) : shared (PMF.pure value) = independent (PMF.pure value) (PMF.pure value) := by
  simp only [shared, independent, PMF.pure_map, PMF.pure_bind]

theorem support_subsingleton (law : PMF A) (copyable : shared law = independent law law) :
    law.support.Subsingleton := by
  intro x one y two
  exact support_shared law x y (copyable.symm ▸ support_independent law law x y one two)

theorem copyable_iff_pure (law : PMF A) :
    shared law = independent law law ↔ ∃ value, law = PMF.pure value := by
  constructor
  · intro copyable
    obtain ⟨value, member⟩ := law.support_nonempty
    have same : ∀ x ∈ law.support, x = value := fun x hx => support_subsingleton law copyable hx member
    have collapsed := bind_congr_of_support law (fun x => PMF.pure x) (fun _ => PMF.pure value)
      (fun x hx => congrArg PMF.pure (same x hx))
    exact ⟨value, by simpa only [PMF.bind_pure, PMF.bind_const] using collapsed⟩
  · rintro ⟨value, rfl⟩
    exact shared_pure value

theorem kernel_copyable_iff_deterministic (kernel : A → PMF B) :
    (∀ input, shared (kernel input) = independent (kernel input) (kernel input)) ↔
      ∃ function : A → B, ∀ input, kernel input = PMF.pure (function input) := by
  constructor
  · intro copyable
    classical
    choose function laws using fun input => (copyable_iff_pure (kernel input)).mp (copyable input)
    exact ⟨function, laws⟩
  · rintro ⟨function, laws⟩ input
    rw [laws input]
    exact shared_pure (function input)

theorem shared_map (law : PMF A) (function : A → B) :
    (shared law).map (fun pair => (function pair.1, function pair.2)) = shared (law.map function) := by
  simp only [shared, PMF.map_comp, Function.comp_def]

theorem independent_map {C D : Type} (first : PMF A) (second : PMF B)
    (one : A → C) (two : B → D) :
    (independent first second).map (fun pair => (one pair.1, two pair.2)) =
      independent (first.map one) (second.map two) := by
  simp only [independent, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]

theorem discard (law : PMF A) : law.map (fun _ => PUnit.unit) = PMF.pure PUnit.unit := PMF.map_const _ _

theorem shared_agreement (law : PMF A) :
    eventProb (shared law) (fun pair => pair.1 = pair.2) = 1 := by
  rw [shared, eventProb_map]
  simp only [eventProb, eq_self, Set.ofPred_true]
  simpa only [PMF.toOuterMeasure_apply, Set.indicator_univ] using law.tsum_coe

theorem fair_independent_agreement :
    eventProb (independent (uniform Bool) (uniform Bool)) (fun pair => pair.1 = pair.2) = 1 / 2 := by
  rw [independent, eventProb_bind_eq]
  have each (x : Bool) : eventProb ((uniform Bool).map (fun y => (x, y))) (fun pair => pair.1 = pair.2) = 1 / 2 := by
    rw [eventProb_map]
    have eventEq : (fun y : Bool => x = y) = (fun y => y = x) := funext (fun _ => propext eq_comm)
    change eventProb (uniform Bool) (fun y => x = y) = _
    rw [eventEq, uniform_guess]
    norm_num
  simp_rw [each]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem fair_not_copyable : shared (uniform Bool) ≠ independent (uniform Bool) (uniform Bool) := by
  intro copyable
  have impossible : false = true := support_subsingleton (uniform Bool) copyable
    (by simp [uniform]) (by simp [uniform])
  cases impossible

end Foundation.Probability.Copyability
