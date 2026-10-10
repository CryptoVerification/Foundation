import Foundation.Crypto.Semantics.Oracle.RandomOracle

/-! Explicit adaptive bounds for output collisions and returns to a fixed
initial value. These are only the first bad events in an indifferentiability
proof; hidden-chain guesses and experiment coupling are separate obligations.
-/
namespace CryptoOracle.RandomOracle

open Foundation.Probability
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Input Output Result : Type} [DecidableEq Input] [DecidableEq Output]
  [Fintype Output] [Nonempty Output]

/-- Tables are stored newest first. Each newly sampled answer must avoid a
list determined before its draw; cached calls do not add a new condition. -/
def Avoided (forbidden : Table Input Output → Input → List Output) : Table Input Output → Prop
  | [] => True
  | (input, output) :: table => output ∉ forbidden table input ∧ Avoided forbidden table

omit [DecidableEq Input] [DecidableEq Output] [Fintype Output] [Nonempty Output] in
/-- Enlarging the forbidden lists strengthens the history invariant. -/
theorem Avoided.mono {small large : Table Input Output → Input → List Output}
    (includes : ∀ table input, small table input ⊆ large table input)
    {table : Table Input Output} (good : Avoided large table) : Avoided small table := by
  induction table with
  | nil => trivial
  | cons entry table ih =>
      exact ⟨fun hm => good.1 (includes table entry.1 hm), ih good.2⟩

omit [DecidableEq Input] [DecidableEq Output] [Fintype Output] [Nonempty Output] in
/-- Every chronological suffix of a good table is good as well. -/
theorem Avoided.append_tail {forbidden : Table Input Output → Input → List Output}
    (later table : Table Input Output) (good : Avoided forbidden (later ++ table)) :
    Avoided forbidden table := by
  induction later with
  | nil => exact good
  | cons entry later ih => exact ih good.2

omit [DecidableEq Output] in
/-- One fresh draw can violate the history invariant only by landing in the
specified list. The list may depend on the full earlier table and new input. -/
theorem step_avoided_bound (forbidden : Table Input Output → Input → List Output)
    (table : Table Input Output) (good : Avoided forbidden table) (input : Input) :
    eventProb (oracle table input) (fun answer => ¬Avoided forbidden answer.1) ≤
      (forbidden table input).length * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  cases ht : table.lookup input with
  | some output =>
      rw [known table input output ht]
      simp [eventProb, good]
  | none =>
      rw [fresh table input ht, eventProb_map]
      have he : (fun output : Output => ¬Avoided forbidden ((input, output) :: table)) =
          (fun output => output ∈ forbidden table input) := by
        funext output
        apply propext
        simp only [Avoided, good, and_true, not_not]
      rw [he]
      exact uniform_mem_list _

omit [DecidableEq Output] in
/-- Adaptive union bound for any pre-draw forbidden lists of at most
`slope * table.length + offset` values. Repeated queries count in q but do not
create new entries. No independence of the adversary's successive inputs is
assumed. This subsumes the output-collision argument below. -/
theorem run_avoided_bound {program : Program Input Output Result} {q : Nat}
    (bound : program.BoundedQueries q)
    (forbidden : Table Input Output → Input → List Output) (slope offset : Nat)
    (size : ∀ table input, (forbidden table input).length ≤ slope * table.length + offset)
    (table : Table Input Output) (good : Avoided forbidden table) :
    eventProb (program.run oracle table) (fun out => ¬Avoided forbidden out.state) ≤
      ((q * (slope * (table.length + q) + offset) : Nat) : ℝ≥0∞) *
        (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  classical
  induction bound generalizing table with
  | done result q => simp [Program.run, eventProb, good]
  | query input next q hb ih =>
      simp only [Program.run]
      calc
        _ ≤ eventProb (oracle table input) (fun answer => ¬Avoided forbidden answer.1) +
            ((q * (slope * (table.length + q + 1) + offset) : Nat) : ℝ≥0∞) *
              (Fintype.card Output : ℝ≥0∞)⁻¹ := by
          apply eventProb_bind_le_bad_add
          intro answer ha hg
          have hgood : Avoided forbidden answer.1 := not_not.mp hg
          have hl := (step table input answer ha).2.2
          rw [eventProb_map]
          refine (ih answer.2 answer.1 hgood).trans ?_
          apply mul_le_mul' _ (le_refl _)
          exact_mod_cast Nat.mul_le_mul_left q (Nat.add_le_add_right
            (Nat.mul_le_mul_left slope (show answer.1.length + q ≤
              table.length + q + 1 by omega)) offset)
        _ ≤ ((slope * table.length + offset : Nat) : ℝ≥0∞) *
              (Fintype.card Output : ℝ≥0∞)⁻¹ +
            ((q * (slope * (table.length + q + 1) + offset) : Nat) : ℝ≥0∞) *
              (Fintype.card Output : ℝ≥0∞)⁻¹ := by
          apply add_le_add _ (le_refl _)
          exact (step_avoided_bound forbidden table good input).trans
            (mul_le_mul' (by exact_mod_cast size table input) (le_refl _))
        _ = ((slope * table.length + offset +
              q * (slope * (table.length + q + 1) + offset) : Nat) : ℝ≥0∞) *
              (Fintype.card Output : ℝ≥0∞)⁻¹ := by simp only [Nat.cast_add, add_mul]
        _ ≤ _ := by
          apply mul_le_mul' _ (le_refl _)
          exact_mod_cast (show slope * table.length + offset +
            q * (slope * (table.length + q + 1) + offset) ≤
            (q + 1) * (slope * (table.length + (q + 1)) + offset) by nlinarith)
  | coin next q hb ih =>
      simp only [Program.run]
      apply eventProb_bind_le
      intro bit
      exact ih bit table good

def FreshOutputs (initial : Output) (table : Table Input Output) : Prop :=
  (table.map Prod.snd).Nodup ∧ initial ∉ table.map Prod.snd

omit [DecidableEq Input] [Fintype Output] [Nonempty Output] in
/-- The output-collision invariant is an instance of the generic pre-draw
avoidance invariant; this keeps the established theorem's statement intact. -/
theorem freshOutputs_iff_avoided (initial : Output) (table : Table Input Output) :
    FreshOutputs initial table ↔
      Avoided (fun earlier _ => initial :: earlier.map Prod.snd) table := by
  induction table with
  | nil => simp [FreshOutputs, Avoided]
  | cons entry table ih =>
      obtain ⟨input, output⟩ := entry
      simp only [FreshOutputs, List.map_cons, List.nodup_cons, List.mem_cons, not_or,
        Avoided] at *
      tauto

/-- The forbidden output list counts earlier sampled values and the initial
value. Repeated requests do not add entries or create a new failure. -/
theorem step_collision_bound (initial : Output) (table : Table Input Output)
    (good : FreshOutputs initial table) (input : Input) :
    eventProb (oracle table input) (fun answer => ¬FreshOutputs initial answer.1) ≤
      (table.length + 1 : Nat) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  simp_rw [freshOutputs_iff_avoided]
  simpa using step_avoided_bound (fun earlier _ => initial :: earlier.map Prod.snd) table
    ((freshOutputs_iff_avoided initial table).mp good) input

/-- A concrete conservative birthday bound for all adaptive calls, derived
from the common history-dependent forbidden-list argument. -/
theorem run_collision_bound {program : Program Input Output Result} {q : Nat}
    (bound : program.BoundedQueries q) (initial : Output) (table : Table Input Output)
    (good : FreshOutputs initial table) :
    eventProb (program.run oracle table) (fun out => ¬FreshOutputs initial out.state) ≤
      ((q * (table.length + q + 1) : Nat) : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  simp_rw [freshOutputs_iff_avoided]
  simpa only [Nat.one_mul, Nat.add_assoc] using
    run_avoided_bound bound (fun earlier _ => initial :: earlier.map Prod.snd) 1 1
      (by intro earlier input; simp) table ((freshOutputs_iff_avoided initial table).mp good)

theorem empty_collision_bound {program : Program Input Output Result} {q : Nat}
    (bound : program.BoundedQueries q) (initial : Output) :
    eventProb (program.run oracle []) (fun out => ¬FreshOutputs initial out.state) ≤
      ((q * (q + 1) : Nat) : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  simpa [FreshOutputs] using run_collision_bound bound initial [] (by simp [FreshOutputs])

end CryptoOracle.RandomOracle
