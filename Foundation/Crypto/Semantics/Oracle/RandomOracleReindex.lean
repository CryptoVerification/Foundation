import Foundation.Crypto.Semantics.Oracle.RandomOracle
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! Injective input encodings preserve the lazy random-oracle experiment.
This is used for disjoint-domain games; it does not permit encodings that alias
public and secret inputs. -/
namespace CryptoOracle.RandomOracle

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Input Target Output Result : Type} [DecidableEq Input] [DecidableEq Target]
  [Fintype Output] [Nonempty Output]

def mapTable (encode : Input → Target) (table : Table Input Output) : Table Target Output :=
  table.map fun entry => (encode entry.1, entry.2)

omit [Fintype Output] [Nonempty Output] in
theorem lookup_mapTable (encode : Input → Target) (injective : Function.Injective encode)
    (table : Table Input Output) (input : Input) :
    (mapTable encode table).lookup (encode input) = table.lookup input := by
  induction table with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨key, value⟩ := entry
      simp only [mapTable, List.map_cons, List.lookup_cons]
      have he : (encode input == encode key) = (input == key) := by
        by_cases h : input = key
        · subst input
          simp
        · simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (injective.ne h)]
      rw [he]
      split <;> simp_all [mapTable]

theorem reindex_step (encode : Input → Target) (injective : Function.Injective encode)
    (table : Table Input Output) (input : Input) :
    (oracle table input).map (fun answer => (mapTable encode answer.1, answer.2)) =
      oracle (mapTable encode table) (encode input) := by
  simp only [oracle, lookup_mapTable encode injective]
  cases he : table.lookup input <;>
    simp [PMF.pure_map, PMF.map_comp, Function.comp_def, mapTable]

/-- Equality includes the final encoded cache, result and original transcript. -/
theorem reindex_run (encode : Input → Target) (injective : Function.Injective encode)
    (program : Program Input Output Result) (table : Table Input Output) :
    (program.run oracle table).map (Program.mapState (mapTable encode)) =
      program.run (Program.adaptOracle encode id oracle) (mapTable encode table) := by
  apply Program.run_state_map
  intro state request
  change _ = PMF.map id _
  rw [PMF.map_id]
  exact reindex_step encode injective state request

/-- An injective input translation preserves the result distribution for
arbitrary adaptive programs, including repeated queries and local coins. -/
theorem reindex_result (encode : Input → Target) (injective : Function.Injective encode)
    (program : Program Input Output Result) (table : Table Input Output) :
    ((program.mapQueries encode id).run oracle (mapTable encode table)).map Outcome.result =
      (program.run oracle table).map Outcome.result := by
  rw [Program.mapQueries_run_result]
  have he := congrArg (PMF.map Outcome.result) (reindex_run encode injective program table)
  simpa only [PMF.map_comp, Program.mapState, Function.comp_def] using he.symm

end CryptoOracle.RandomOracle
