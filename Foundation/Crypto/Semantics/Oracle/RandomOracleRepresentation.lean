import Foundation.Crypto.Semantics.Oracle.RandomOracle
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! Operational lazy oracles with a different stored response type. Cached
responses are decoded before return; fresh public responses are encoded for
storage. The adaptive program and public trace remain unchanged. -/
namespace CryptoOracle.RandomOracle.Representation
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Input Response Stored Result : Type} [DecidableEq Input]

variable (codec : Input → Response ≃ Stored)

def table (plain : Table Input Response) : Table Input Stored :=
  plain.map fun entry => (entry.1, codec entry.1 entry.2)

theorem lookup (plain : Table Input Response) (input : Input) :
    (table codec plain).lookup input = (plain.lookup input).map (codec input) := by
  induction plain with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨key, value⟩ := entry
      simp only [table, List.map_cons, List.lookup_cons]
      by_cases same : input = key
      · subst key; simp
      · simp only [beq_eq_false_iff_ne.mpr same]
        exact ih

omit [DecidableEq Input] in
theorem table_inverse (plain : Table Input Response) :
    table (fun input => (codec input).symm) (table codec plain) = plain := by
  simp only [table, List.map_map, Function.comp_def, Equiv.symm_apply_apply]
  exact List.map_id _

omit [DecidableEq Input] in
theorem table_length (plain : Table Input Response) : (table codec plain).length = plain.length := by
  simp [table]

variable [Fintype Response] [Nonempty Response]

noncomputable def oracle : Oracle Input Response (Table Input Stored) :=
  fun saved input => match saved.lookup input with
  | some value => PMF.pure (saved, (codec input).symm value)
  | none => (uniform Response).map fun response => ((input, codec input response) :: saved, response)

theorem step (plain : Table Input Response) (input : Input) :
    (RandomOracle.oracle plain input).map (fun answer => (table codec answer.1, answer.2)) =
      oracle codec (table codec plain) input := by
  simp only [oracle, RandomOracle.oracle, lookup]
  cases found : plain.lookup input <;>
    simp [table, PMF.map_comp, Function.comp_def, PMF.pure_map]

/-- All programs, including adaptive queries, repeats and local coins. -/
theorem run (program : Program Input Response Result) (plain : Table Input Response) :
    (program.run RandomOracle.oracle plain).map (Program.mapState (table codec)) =
      program.run (oracle codec) (table codec plain) := by
  apply Program.run_state_map
  exact step codec

/-- Complete decoding, not merely result erasure. -/
theorem decoded_run (program : Program Input Response Result) (plain : Table Input Response) :
    (program.run (oracle codec) (table codec plain)).map
      (Program.mapState (table (fun input => (codec input).symm))) =
      program.run RandomOracle.oracle plain := by
  rw [← run, PMF.map_comp]
  have maps : (Program.mapState (table (fun input => (codec input).symm))) ∘
      (Program.mapState (table codec)) = (id : Outcome Input Response Result (Table Input Response) → _) := by
    funext out
    cases out
    simp only [Function.comp_def, Program.mapState, table_inverse, id_eq]
  rw [maps, PMF.map_id]

end CryptoOracle.RandomOracle.Representation
