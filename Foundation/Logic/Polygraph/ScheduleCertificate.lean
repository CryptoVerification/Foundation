import Foundation.Logic.Polygraph.StateCube
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A precise comparison with literal enumeration of all transformation orders.
The size is a number of certificate slots / listed path nodes, not bytes of a
Lean proof term and not a lower bound on arbitrary proof systems. Local slots
are state-parametric statements; their proof payloads are not charged here.
The generic reconstruction theorem is shared by every instance. -/
namespace Foundation.Logic.Polygraph.ScheduleCertificate

universe u

abbrev Schedule (n : Nat) := Equiv.Perm (Fin n)

def order {n : Nat} (schedule : Schedule n) : List (Fin n) := List.ofFn schedule

theorem order_length {n : Nat} (schedule : Schedule n) : (order schedule).length = n := by
  simp [order]

theorem order_perm {n : Nat} (schedule : Schedule n) :
    (order schedule).Perm (List.finRange n) := by
  simpa only [order, Function.id_comp, List.ofFn_id] using
    schedule.ofFn_comp_perm (id : Fin n → Fin n)

theorem order_injective {n : Nat} : Function.Injective (@order n) := by
  intro a b same
  apply Equiv.ext
  intro x
  exact congrFun (List.ofFn_inj.mp same) x

theorem schedule_count (n : Nat) : Fintype.card (Schedule n) = n.factorial := by
  simp [Schedule, Fintype.card_perm]

/-- Raw state operations; no commuting laws are built into this presentation. -/
structure Presentation (n : Nat) where
  State : Type u
  vertex : State → Finset (Fin n)
  step : Fin n → State → State

/-- One slot per vertex law, present-label law, and ordered square.
Diagonal square slots have an impossible freshness premise and are harmless.
Using all ordered pairs keeps the accounting simple and conservative. -/
abbrev LocalSlot (n : Nat) := Fin n ⊕ (Fin n ⊕ (Fin n × Fin n))

def Presentation.Statement {n : Nat} (P : Presentation.{u} n) : LocalSlot n → Prop
  | .inl i => ∀ x, P.vertex (P.step i x) = insert i (P.vertex x)
  | .inr (.inl i) => ∀ x, i ∈ P.vertex x → P.step i x = x
  | .inr (.inr (i, j)) => ∀ x, i ≠ j → i ∉ P.vertex x → j ∉ P.vertex x →
      P.step j (P.step i x) = P.step i (P.step j x)

/-- No path-indexed proof is stored: only the finite local obligations above. -/
structure LocalCertificate {n : Nat} (P : Presentation.{u} n) : Type where
  prove : ∀ slot, P.Statement slot

def LocalCertificate.toCube {n : Nat} {P : Presentation.{u} n}
    (certificate : LocalCertificate P) : StateCube (Fin n) where
  State := P.State
  vertex := P.vertex
  step := P.step
  vertex_step i := certificate.prove (.inl i)
  step_present i := certificate.prove (.inr (.inl i))
  square i j := certificate.prove (.inr (.inr (i, j)))

/-- The finite certificate proves all n! complete orders at once. -/
theorem LocalCertificate.all_orders {n : Nat} {P : Presentation.{u} n}
    (certificate : LocalCertificate P) (schedule : Schedule n) (x : P.State) :
    certificate.toCube.run (order schedule) x =
      certificate.toCube.run (List.finRange n) x :=
  certificate.toCube.run_perm (order_perm schedule) x

/-- The equality has a comparison made of actual contextual square generators. -/
theorem LocalCertificate.comparison {n : Nat} {P : Presentation.{u} n}
    (_certificate : LocalCertificate P) (schedule : Schedule n) :
    Nonempty (StateCube.Comparison (order schedule) (List.finRange n)) :=
  StateCube.comparison_complete (order_perm schedule)

theorem local_slot_count (n : Nat) : Fintype.card (LocalSlot n) = n * n + 2 * n := by
  simp [LocalSlot, Fintype.card_sum, Fintype.card_prod]
  omega

/-- Add one slot for the canonical cryptographic argument. This argument may
be large; its payload is shared, and is not being called a one-node Lean proof. -/
def sharedSize (n : Nat) : Nat := Fintype.card (LocalSlot n) + 1

theorem shared_size (n : Nat) : sharedSize n = (n + 1) ^ 2 := by
  rw [sharedSize, local_slot_count]
  ring

/-- A finite family of local statements and one canonical argument. `Goal`
may inspect the entire state transformer, including its private state. -/
structure SharedCertificate {n : Nat} (P : Presentation.{u} n)
    (Goal : (P.State → P.State) → Prop) : Type where
  laws : LocalCertificate P
  canonical : Goal (laws.toCube.run (List.finRange n))

theorem SharedCertificate.sound {n : Nat} {P : Presentation.{u} n}
    {Goal : (P.State → P.State) → Prop} (certificate : SharedCertificate P Goal)
    (schedule : Schedule n) : Goal (certificate.laws.toCube.run (order schedule)) := by
  have same : certificate.laws.toCube.run (order schedule) =
      certificate.laws.toCube.run (List.finRange n) := by
    funext state
    exact certificate.laws.all_orders schedule state
  rw [same]
  exact certificate.canonical

/-- A literal table must contain a certified row for every complete order.
Rows may repeat; allowing repetition only increases the lower bound. -/
structure ExplicitCertificate (n : Nat) (Goal : Schedule n → Prop) where
  rows : List (Schedule n)
  complete : ∀ schedule, schedule ∈ rows
  valid : ∀ schedule ∈ rows, Goal schedule

def ExplicitCertificate.size {n : Nat} {Goal : Schedule n → Prop}
    (certificate : ExplicitCertificate n Goal) : Nat :=
  (certificate.rows.map (fun schedule => (order schedule).length + 1)).sum

theorem ExplicitCertificate.rows_lower_bound {n : Nat} {Goal : Schedule n → Prop}
    (certificate : ExplicitCertificate n Goal) : n.factorial ≤ certificate.rows.length := by
  classical
  have all : certificate.rows.toFinset = Finset.univ := by
    ext schedule
    simp [certificate.complete schedule]
  calc
    _ = certificate.rows.toFinset.card := by rw [all]; simp [schedule_count]
    _ ≤ _ := List.toFinset_card_le _

theorem ExplicitCertificate.size_eq {n : Nat} {Goal : Schedule n → Prop}
    (certificate : ExplicitCertificate n Goal) :
    certificate.size = (n + 1) * certificate.rows.length := by
  simp [size, order_length, List.map_const', List.sum_replicate, Nat.mul_comm]

theorem ExplicitCertificate.size_lower_bound {n : Nat} {Goal : Schedule n → Prop}
    (certificate : ExplicitCertificate n Goal) :
    (n + 1) * n.factorial ≤ certificate.size := by
  rw [certificate.size_eq]
  exact Nat.mul_le_mul_left _ certificate.rows_lower_bound

/-- Tightness of the table bound: enumerate each schedule exactly once. -/
noncomputable def enumerate {n : Nat} {Goal : Schedule n → Prop}
    (proof : ∀ schedule, Goal schedule) : ExplicitCertificate n Goal where
  rows := Finset.univ.toList
  complete schedule := by simp
  valid schedule _ := proof schedule

theorem enumerate_size {n : Nat} {Goal : Schedule n → Prop} (proof : ∀ s, Goal s) :
    (enumerate proof).size = (n + 1) * n.factorial := by
  rw [ExplicitCertificate.size_eq]
  simp [enumerate, schedule_count]

theorem succ_lt_factorial {n : Nat} (large : 3 ≤ n) : n + 1 < n.factorial := by
  induction n, large using Nat.le_induction with
  | base => decide
  | succ n large ih =>
      rw [Nat.factorial_succ]
      nlinarith

/-- Strict separation for every n≥3, within the two declared formats. -/
theorem smaller_than_enumeration {n : Nat} (large : 3 ≤ n)
    {Goal : Schedule n → Prop} (certificate : ExplicitCertificate n Goal) :
    sharedSize n < certificate.size := by
  rw [shared_size]
  calc
    _ < (n + 1) * n.factorial := by
      simpa [pow_two] using Nat.mul_lt_mul_of_pos_left (succ_lt_factorial large)
        (Nat.succ_pos n)
    _ ≤ _ := certificate.size_lower_bound

end Foundation.Logic.Polygraph.ScheduleCertificate
