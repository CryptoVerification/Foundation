import Foundation.Crypto.Semantics.Oracle.RandomOracleValues
import Foundation.Crypto.Semantics.Oracle.RandomOracleCollision

/-! Collision and fixed-value avoidance for a sampled finite function, derived
from the existing lazy-oracle birthday bound. Enumerating the finite inputs is
proof instrumentation, not a machine implementation or an infinite table. -/
namespace CryptoOracle.RandomOracle

open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Input Output : Type} [DecidableEq Input] [Fintype Output] [Nonempty Output]

/-- Read a specified finite list through the existing oracle interface. -/
def readCoordinates : List Input → Program Input Output Unit
  | [] => .done ()
  | input :: rest => .query input (fun _ => readCoordinates rest)

omit [DecidableEq Input] [Fintype Output] [Nonempty Output] in
theorem readCoordinates_queries (inputs : List Input) :
    (readCoordinates (Output := Output) inputs).BoundedQueries inputs.length := by
  induction inputs with
  | nil => exact .done _ 0
  | cons input rest ih => exact .query input _ rest.length (fun _ => ih)

/-- Every enumerated coordinate is stored with its fixed function value at
completion. Cached inputs and repeated list elements are allowed. -/
theorem readCoordinates_stored (function : Input → Output) (inputs : List Input) (table : Table Input Output)
    (values : TableValues function table) (out : Outcome Input Output Unit (Table Input Output))
    (support : out ∈ ((readCoordinates inputs).run (eager function) table).support) :
    ∀ input ∈ inputs, (input, function input) ∈ out.state := by
  induction inputs generalizing table out with
  | nil => intro input member; cases member
  | cons input rest ih =>
      rw [readCoordinates, Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, step, support⟩ := support
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨tail, reachable, rfl⟩ := support
      have nextValues := (eager_step_values function table values input answer step).1
      have present : (input, function input) ∈ answer.1 := by
        cases known : table.lookup input with
        | none =>
            simp only [eager, known, PMF.mem_support_pure_iff] at step
            subst answer
            exact List.mem_cons_self
        | some output =>
            simp only [eager, known, PMF.mem_support_pure_iff] at step
            subst answer
            obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp known
            have member : (input, output) ∈ table := by rw [same]; simp
            simpa only [values.lookup known] using member
      intro query member
      rcases List.mem_cons.mp member with rfl | old
      · exact run_table_subset (readCoordinates rest) answer.1 tail
          (eager_run_support function _ _ tail reachable) present
      · exact ih answer.1 nextValues tail reachable query old

omit [DecidableEq Input] [Fintype Output] [Nonempty Output] in
/-- A fresh complete finite cache implies injectivity and avoidance of the
specified value for its fixed function. This is a deterministic implication. -/
theorem fresh_complete_function (function : Input → Output) (initial : Output)
    (table : Table Input Output) (stored : ∀ input, (input, function input) ∈ table)
    (fresh : FreshOutputs initial table) :
    Function.Injective function ∧ ∀ input, function input ≠ initial := by
  constructor
  · intro left right same
    have entries := List.inj_on_of_nodup_map fresh.1 (stored left) (stored right) same
    exact congrArg Prod.fst entries
  · intro input equal
    apply fresh.2
    exact List.mem_map.mpr ⟨(input, function input), stored input, equal⟩

/-- A conservative explicit bound on failure of injectivity or fixed-value
avoidance for the whole sampled finite function. It reuses eager/lazy equality
and the adaptive lazy-oracle birthday bound, rather than assuming independence
of values which have already been exposed in a cryptographic experiment. -/
theorem uniform_function_bad_bound [Fintype Input] (initial : Output) :
    eventProb (uniform (Input → Output))
      (fun function => ¬(Function.Injective function ∧ ∀ input, function input ≠ initial)) ≤
      ((Fintype.card Input * (Fintype.card Input + 1) : Nat) : ℝ≥0∞) *
        (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  classical
  let inputs : List Input := Finset.univ.toList
  let program : Program Input Output Unit := readCoordinates inputs
  let joint := (uniform (Input → Output)).bind (fun function =>
    (program.run (eager function) []).map (fun out => (function, out)))
  have const {A B : Type} (law : PMF A) (value : B) : law.map (fun _ => value) = PMF.pure value := by
    change law.map (Function.const A value) = _
    exact PMF.map_const _ _
  have first : joint.map Prod.fst = uniform (Input → Output) := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp_rw [const]
    exact PMF.bind_pure _
  have second : joint.map Prod.snd = program.run oracle [] := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    have identity : (fun out : Outcome Input Output Unit (Table Input Output) => out) = id := rfl
    simp only [identity, PMF.map_id]
    exact eager_lazy program []
  calc
    _ = eventProb joint (fun pair => ¬(Function.Injective pair.1 ∧ ∀ input, pair.1 input ≠ initial)) := by
      rw [← first, eventProb_map]
    _ ≤ eventProb joint (fun pair => ¬FreshOutputs initial pair.2.state) := by
      apply eventProb_mono_of_support
      intro pair reachable bad good
      rw [PMF.mem_support_bind_iff] at reachable
      obtain ⟨function, _, reachable⟩ := reachable
      rw [PMF.mem_support_map_iff] at reachable
      obtain ⟨out, reachable, rfl⟩ := reachable
      apply bad
      apply fresh_complete_function function initial out.state _ good
      intro input
      exact readCoordinates_stored function inputs [] (by intro entry member; cases member) out reachable input
        (Finset.mem_toList.mpr (Finset.mem_univ input))
    _ = eventProb (program.run oracle []) (fun out => ¬FreshOutputs initial out.state) := by
      rw [← second, eventProb_map]
    _ ≤ _ := by
      have bound := empty_collision_bound (readCoordinates_queries (Output := Output) inputs) initial
      simpa only [program, inputs, Finset.length_toList, Finset.card_univ] using bound

end CryptoOracle.RandomOracle
