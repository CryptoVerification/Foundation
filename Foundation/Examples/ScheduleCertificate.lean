import Foundation.Constructions.Symmetric.RandomFunctionMACSchedules

/-! The same chosen-message forgery claim in the shared and literal formats.
The numerical examples count certificate structure, not kernel time or bytes. -/
namespace Foundation.Symmetric.RandomFunctionMACSchedules.Examples

open Foundation.Probability Foundation.Logic.Polygraph.ScheduleCertificate CryptoOracle
open scoped ENNReal

/-- Three signing queries: one depends on a local coin, one on the first tag,
and one repeats the first query. Message 7 is then forged. -/
def attack : Program (Fin 8) (Fin 256) (Fin 8 × Fin 256) :=
  .coin fun coin =>
    let first : Fin 8 := if coin then 0 else 1
    .query first fun tag =>
      .query (if tag.val % 2 = 0 then 2 else 3) fun second =>
        .query first fun repeated =>
          .done (7, if coin then repeated else second)

theorem attack_queries : attack.BoundedQueries 3 :=
  .coin _ _ (fun _ => .query _ _ 2 (fun _ => .query _ _ 1 (fun _ =>
    .query _ _ 0 (fun _ => .done _ 0))))

theorem reduction_queries : (checkedAttack [] attack).BoundedQueries 4 :=
  checkedAttack_queries attack_queries []

theorem forgery_bound : ∀ schedule : Schedule 8,
    eventProb (scheduledGame attack schedule) (· = true) ≤ (256 : ℝ≥0∞)⁻¹ := by
  simpa using all_schedules_secure attack

/-- An actual literal certificate for the very same security proposition.
It is a mathematical enumeration, not used to prove `forgery_bound`. -/
noncomputable def explicit : ExplicitCertificate 8 (fun schedule =>
    eventProb (scheduledGame attack schedule) (· = true) ≤ (256 : ℝ≥0∞)⁻¹) :=
  enumerate forgery_bound

theorem explicit_rows : explicit.rows.length = 40320 := by
  change (Finset.univ : Finset (Schedule 8)).toList.length = _
  simp [schedule_count, Nat.factorial]

theorem explicit_nodes : explicit.size = 362880 := by
  exact enumerate_size forgery_bound

theorem shared_slots : sharedSize 8 = 81 := by
  rw [shared_size]
  decide

theorem strict_separation : sharedSize 8 < explicit.size :=
  smaller_than_enumeration (by omega) explicit

/-- The keyed construction also has a concrete reduction bound. A PRF bound
epsilon for this four-query distinguisher gives epsilon + 1/256 for forgery. -/
theorem keyed_forgery_bound {Key : Type} (keys : PMF Key)
    (evaluate : Key → Fin 8 → Fin 256) (epsilon : ℝ≥0∞)
    (prf : eventProb (familyExperiment keys evaluate (checkedAttack [] attack)) (· = true) ≤
      eventProb (idealExperiment (checkedAttack [] attack)) (· = true) + epsilon) :
    eventProb (keyedGame keys evaluate attack) (· = true) ≤ epsilon + (256 : ℝ≥0∞)⁻¹ := by
  simpa using keyed_secure keys evaluate attack epsilon prf

/-- info: [(4, 24, 120, 25), (8, 40320, 362880, 81), (12, 479001600, 6227020800, 169)] -/
#guard_msgs in
#eval [4, 8, 12].map fun n =>
  (n, n.factorial, (n + 1) * n.factorial, (n + 1) ^ 2)

/- This check really constructs all listed paths, rather than evaluating
the factorial formula. The generic proofs above never run this enumeration.
-/
/-- info: [(4, 24, 120, 25), (8, 40320, 362880, 81)] -/
#guard_msgs in
#eval [4, 8].map fun n =>
  let rows := (List.finRange n).permutations
  (n, rows.length, (rows.map (fun row => row.length + 1)).sum, (n + 1) ^ 2)

end Foundation.Symmetric.RandomFunctionMACSchedules.Examples
