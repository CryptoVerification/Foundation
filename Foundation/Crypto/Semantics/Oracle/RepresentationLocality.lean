import Foundation.Crypto.Semantics.Oracle.QueryFootprint
import Foundation.Crypto.Semantics.Oracle.RandomOracleRepresentation

/-! Locality for actual operational cache encodings. Unqueried codec entries
do not affect execution from a COMMON stored cache. If initial public caches
are encoded separately, their encodings must also agree. -/
namespace CryptoOracle.RandomOracle.Representation
open Foundation.Probability
variable {Input Response Stored Result : Type} [DecidableEq Input]
  [Fintype Response] [Nonempty Response]

theorem oracle_congr_at (left right : Input → Response ≃ Stored) (input : Input)
    (agree : left input = right input) (saved : Table Input Stored) :
    oracle left saved input = oracle right saved input := by
  simp only [oracle, agree]

theorem run_congr_on_footprint (left right : Input → Response ≃ Stored)
    (program : Program Input Response Result)
    (agree : ∀ input ∈ program.footprint, left input = right input) (saved : Table Input Stored) :
    program.run (oracle left) saved = program.run (oracle right) saved := by
  apply Program.run_congr_on_footprint
  intro input member state
  exact oracle_congr_at left right input (agree input member) state

/-- A patch outside the extracted effect set needs no new local oracle law
for this program. This theorem compares raw stored outcomes, without decoding. -/
theorem run_unaffected_patch (left right : Input → Response ≃ Stored) (changed : Finset Input)
    (agree : ∀ input ∉ changed, left input = right input) (program : Program Input Response Result)
    (unaffected : Disjoint program.footprint changed) (saved : Table Input Stored) :
    program.run (oracle left) saved = program.run (oracle right) saved := by
  apply run_congr_on_footprint
  intro input member
  exact agree input (fun changedMember => Finset.disjoint_left.mp unaffected member changedMember)

theorem run_unaffected_positions (left right : Input → Response ≃ Stored) (changed : Finset Input)
    (agree : ∀ input ∉ changed, left input = right input) (program : Program Input Response Result)
    (bound : Nat) (bounded : program.BoundedQueries bound)
    (unaffected : Program.affectedPositions changed bound program = []) (saved : Table Input Stored) :
    program.run (oracle left) saved = program.run (oracle right) saved :=
  run_unaffected_patch left right changed agree program ((bounded.unaffected_iff changed).mpr unaffected) saved

omit [DecidableEq Input] [Fintype Response] [Nonempty Response] in
theorem table_eq_of_agree (left right : Input → Response ≃ Stored) (plain : Table Input Response)
    (agree : ∀ input response, (input, response) ∈ plain → left input = right input) :
    table left plain = table right plain := by
  unfold table
  apply List.map_congr_left
  rintro ⟨input, response⟩ member
  simp only [agree input response member]

theorem encoded_run_unaffected_patch (left right : Input → Response ≃ Stored) (changed : Finset Input)
    (agree : ∀ input ∉ changed, left input = right input) (program : Program Input Response Result)
    (unaffected : Disjoint program.footprint changed) (plain : Table Input Response)
    (initial : ∀ input response, (input, response) ∈ plain → input ∉ changed) :
    program.run (oracle left) (table left plain) = program.run (oracle right) (table right plain) := by
  rw [table_eq_of_agree left right plain (fun input response member => agree input (initial input response member))]
  exact run_unaffected_patch left right changed agree program unaffected _

/-- The plain lazy cache starts empty and only stores extracted addresses.
An explicit upper set avoids having to expand the full syntactic tree at uses. -/
theorem plain_entries_in_set (program : Program Input Response Result) (allowed : Finset Input)
    (within : program.footprint ⊆ allowed)
    (out : Outcome Input Response Result (Table Input Response))
    (supported : out ∈ (program.run RandomOracle.oracle []).support) :
    ∀ entry ∈ out.state, entry.1 ∈ allowed := by
  intro entry member
  have inTrace : entry ∈ out.trace := by
    simpa using RandomOracle.run_entries program [] out supported member
  exact within (Program.footprint_trace program RandomOracle.oracle [] out supported entry inTrace)

end CryptoOracle.RandomOracle.Representation
