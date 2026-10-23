import Foundation.Crypto.Logic.Polygraph.StateCube

/-! Executable commuting updates, a shared bad event of probability 1/2,
and a square whose individually valid couplings have no common realization. -/
namespace Foundation.Logic.Polygraph.Examples.StateCube

open Foundation.Probability
open CryptoLogic.Polygraph.StateCube
open scoped ENNReal

def flip (i : Bool) (x : Bool × Bool) : Bool × Bool :=
  if i then (!x.1, x.2) else (x.1, !x.2)

theorem flip_commutes (i j : Bool) (x : Bool × Bool) :
    flip j (flip i x) = flip i (flip j x) := by
  cases i <;> cases j <;> simp [flip]

def flips : Polygraph.StateCube Bool := .ofCommuting flip flip_commutes

theorem reordered (x : flips.State) :
    flips.run [false, true] x = flips.run [true, false] x :=
  flips.run_perm (.swap _ _ []) x

def squareComparison : Polygraph.StateCube.Comparison [false, true] [true, false] :=
  .step (.adjacent [] [] false true)

theorem compared (x : flips.State) :
    flips.run [false, true] x = flips.run [true, false] x :=
  flips.comparison_sound squareComparison x

-- Both requested states reuse the very same retained initial state.
/-- info: ((true, true), (true, true), 2) -/
#guard_msgs in
#eval let root : flips.State := (∅, (false, false))
  ((flips.run [false, true] root).2, (flips.run [true, false] root).2,
    (flips.runCount [false, true] root).2)

namespace Growing

/-- The payload type grows with the set of allocated slots. -/
def Payload (S : Finset Nat) := {i // i ∈ S} → Bool

def allocate (S : Finset Nat) (i : Nat) (x : Payload S) : Payload (insert i S) :=
  fun k => if h : k.1 ∈ S then x ⟨k.1, h⟩ else false

theorem payload_heq {S T : Finset Nat} (h : S = T) (x : Payload S) (y : Payload T)
    (agree : ∀ i hi hj, x ⟨i, hi⟩ = y ⟨i, hj⟩) : HEq x y := by
  subst T
  apply heq_of_eq
  funext i
  exact agree i.1 i.2 i.2

theorem allocate_present (S : Finset Nat) (i : Nat) (x : Payload S) (hi : i ∈ S) :
    HEq (allocate S i x) x := by
  apply payload_heq (Finset.insert_eq_of_mem hi)
  intro k _ hk
  simp [allocate, hk]

theorem allocate_square (S : Finset Nat) (i j : Nat) (x : Payload S)
    (_hij : i ≠ j) (_hi : i ∉ S) (_hj : j ∉ S) :
    HEq (allocate (insert i S) j (allocate S i x))
      (allocate (insert j S) i (allocate S j x)) := by
  apply payload_heq (Finset.insert_comm j i S)
  intro k _ _
  by_cases hk : k ∈ S
  · simp [allocate, hk]
  · by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [allocate]

def cube : Polygraph.StateCube Nat :=
  .ofFamily Payload allocate allocate_present allocate_square

def zeros (S : Finset Nat) : Payload S := fun _ => false

theorem allocate_zeros (S : Finset Nat) (i : Nat) :
    allocate S i (zeros S) = zeros (insert i S) := by
  funext k
  simp [allocate, zeros]

/-- These laws are specified at each dependent payload type, before lifting
them to the total-state representation. No fresh randomness is asserted. -/
noncomputable def measured : Measured cube := Measured.ofFamily
  Payload allocate allocate_present allocate_square (fun S => PMF.pure (zeros S))
  (fun S i _ => by rw [PMF.pure_map, allocate_zeros])

theorem global_marginal (S : Finset Nat) :
    measured.joint.map (fun a => a S) = (PMF.pure (zeros S)).map (Sigma.mk S) :=
  measured.joint_marginal S

theorem order_independent (x : cube.State) :
    cube.run [2, 7] x = cube.run [7, 2] x :=
  cube.comparison_sound (.step (.adjacent [] [] 2 7)) x

end Growing

/-- Recording changes while retaining one bit gives cubes of arbitrary size. -/
def retained : Polygraph.StateCube Nat := .ofCommuting
  (fun _ (b : Bool) => b) (fun _ _ _ => rfl)

noncomputable def root : PMF retained.State :=
  (uniform Bool).map (fun b => (∅, b))

theorem root_supported (x : retained.State) (hx : x ∈ root.support) :
    retained.vertex x = ∅ := by
  obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  rfl

noncomputable def measured : Measured retained :=
  Measured.fromRoot retained root root_supported

def bad (x : retained.State) : Prop := x.2 = true

def event (S : Finset Nat) (x : retained.State) : Prop := S.Nonempty ∧ x.2 = true

theorem retained_step_bit (i : Nat) (x : retained.State) :
    (retained.step i x).2 = x.2 := by
  change (if i ∈ x.1 then x else (insert i x.1, x.2)).2 = x.2
  by_cases hi : i ∈ x.1 <;> simp [hi]

theorem retained_query_bit (x : retained.State) (S : Finset Nat) :
    (retained.query x S).2 = x.2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [retained.query_insert, retained_step_bit, ih]

theorem bad_probability : eventProb (measured.law ∅) bad = 1 / 2 := by
  change eventProb ((Measured.fromRoot retained root root_supported).law ∅) bad = _
  rw [Measured.fromRoot_empty]
  change eventProb ((uniform Bool).map (fun b => ((∅, b) : Finset Nat × Bool)))
    (fun x => x.2 = true) = _
  rw [eventProb_map]
  change eventProb (uniform Bool) (· = true) = _
  rw [uniform_guess]
  norm_num

/-- The same event of probability 1/2 controls every endpoint, independently
of how many changes have been recorded. -/
theorem shared_bad_bound (S : Finset Nat) :
    probabilityGap (eventProb (measured.law ∅) (event ∅))
      (eventProb (measured.law S) (event S)) ≤ 1 / 2 := by
  rw [← bad_probability]
  apply measured.common_bad_bound event bad
  intro x _hx hb T i _hi
  have hbit : (retained.query x T).2 ≠ true := by
    rw [retained_query_bit]
    exact hb
  simp [event, retained_step_bit, hbit]

theorem endpoint_probability {S : Finset Nat} (hS : S.Nonempty) :
    eventProb (measured.law S) (event S) = 1 / 2 := by
  rw [← measured.query_law S, eventProb_map]
  simp only [event, hS, true_and, retained_query_bit]
  exact bad_probability

theorem endpoint_gap {S : Finset Nat} (hS : S.Nonempty) :
    probabilityGap (eventProb (measured.law ∅) (event ∅))
      (eventProb (measured.law S) (event S)) = 1 / 2 := by
  rw [endpoint_probability hS]
  have empty_prob : eventProb (measured.law ∅) (event ∅) = 0 := by
    simp [event, eventProb]
  rw [empty_prob]
  simp [probabilityGap]

namespace Obstruction

/-- Equal and opposite fair-bit pairs both have correct fair marginals. -/
noncomputable def equalPair : PMF (Bool × Bool) :=
  (uniform Bool).map (fun b => (b, b))

noncomputable def oppositePair : PMF (Bool × Bool) :=
  (uniform Bool).map (fun b => (b, !b))

theorem equal_left : equalPair.map Prod.fst = uniform Bool := by
  rw [equalPair, PMF.map_comp]
  exact PMF.map_id _

theorem equal_right : equalPair.map Prod.snd = uniform Bool := by
  rw [equalPair, PMF.map_comp]
  exact PMF.map_id _

theorem opposite_left : oppositePair.map Prod.fst = uniform Bool := by
  rw [oppositePair, PMF.map_comp]
  exact PMF.map_id _

theorem opposite_right : oppositePair.map Prod.snd = uniform Bool := by
  rw [oppositePair, PMF.map_comp]
  exact uniform_map_equiv ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩

theorem equal_support (p : Bool × Bool) (hp : p ∈ equalPair.support) : p.1 = p.2 := by
  obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  rfl

theorem opposite_support (p : Bool × Bool) (hp : p ∈ oppositePair.support) : p.1 ≠ p.2 := by
  obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  cases b <;> decide

/-- The four vertices are numbered 00,10,01,11 as 0,1,2,3.
Three equalities and one opposite-bit edge cannot share a root sample. -/
theorem no_assignment (a : Fin 4 → Bool)
    (h01 : a 0 = a 1) (h13 : a 1 = a 3)
    (h02 : a 0 = a 2) (h23 : a 2 ≠ a 3) : False :=
  h23 (h02.symm.trans (h01.trans h13))

/-- Even though every individual edge has fair marginals, no joint PMF has
all four of the specified pair laws. This is stronger than a point example. -/
theorem no_joint (p : PMF (Fin 4 → Bool))
    (h01 : p.map (fun a => (a 0, a 1)) = equalPair)
    (h13 : p.map (fun a => (a 1, a 3)) = equalPair)
    (h02 : p.map (fun a => (a 0, a 2)) = equalPair)
    (h23 : p.map (fun a => (a 2, a 3)) = oppositePair) : False := by
  obtain ⟨a, ha⟩ := p.support_nonempty
  have mapped (i j : Fin 4) : (a i, a j) ∈ (p.map (fun a => (a i, a j))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨a, ha, rfl⟩
  exact no_assignment a
    (equal_support _ (h01 ▸ mapped 0 1))
    (equal_support _ (h13 ▸ mapped 1 3))
    (equal_support _ (h02 ▸ mapped 0 2))
    (opposite_support _ (h23 ▸ mapped 2 3))

end Obstruction
end Foundation.Logic.Polygraph.Examples.StateCube
