import Foundation.Constructions.Hash.Expansion

/-! Chronological graph freshness for ideal compression calls. Besides output
collisions, a new output avoids every earlier input chaining value and its own
input value. This is the bad1/bad2 part of the CSF 2012 complete-chain argument;
it does not bound guesses of hidden internal values (bad3). -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Result : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

def graphForbidden (initial : Digest) (table : CompressionTable Payload Digest)
    (input : CompressionInput Payload Digest) : List Digest :=
  initial :: input.1 :: (table.map Prod.snd ++ table.map (fun entry => entry.1.1))

/-- The table order is the actual reverse sampling order of the lazy oracle. -/
def ForwardFresh (initial : Digest) (table : CompressionTable Payload Digest) : Prop :=
  RandomOracle.Avoided (graphForbidden initial) table

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem graphForbidden_length (initial : Digest) (table : CompressionTable Payload Digest)
    (input : CompressionInput Payload Digest) :
    (graphForbidden initial table input).length = 2 * table.length + 2 := by
  simp [graphForbidden, Nat.two_mul, Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
theorem ForwardFresh.outputs {initial : Digest} {table : CompressionTable Payload Digest}
    (good : ForwardFresh initial table) : RandomOracle.FreshOutputs initial table := by
  rw [RandomOracle.freshOutputs_iff_avoided]
  apply RandomOracle.Avoided.mono (large := graphForbidden initial) _ good
  intro earlier input value hm
  simp only [graphForbidden, List.mem_cons, List.mem_append] at *
  tauto

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- In particular no sampled compression entry is a fixed point. -/
theorem ForwardFresh.no_fixed_point {initial : Digest} {table : CompressionTable Payload Digest}
    (good : ForwardFresh initial table) (entry : CompressionInput Payload Digest × Digest)
    (mem : entry ∈ table) : entry.2 ≠ entry.1.1 := by
  induction table with
  | nil => simp at mem
  | cons head table ih =>
      rcases List.mem_cons.mp mem with he | hm
      · subst entry
        exact fun he => good.1 (by simp [graphForbidden, he])
      · exact ih good.2 hm

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- A newly sampled output cannot equal a chaining value of any older input.
The prefix records entries sampled later than `entry`, not earlier than it. -/
theorem ForwardFresh.no_backward_edge (initial : Digest)
    (later earlier : CompressionTable Payload Digest)
    (entry : CompressionInput Payload Digest × Digest)
    (good : ForwardFresh initial (later ++ entry :: earlier))
    (older : CompressionInput Payload Digest × Digest) (mem : older ∈ earlier) :
    entry.2 ≠ older.1.1 := by
  induction later with
  | nil =>
      exact fun he => good.1 (by
        simp only [graphForbidden, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨older, mem, he.symm⟩))))
  | cons head later ih => exact ih good.2

/-- Adaptive bad1/bad2 bound, starting from any already-good chronological
compression table. Every internal or public call counts in the certificate. -/
theorem run_forward_failure_bound {program : Program (CompressionInput Payload Digest) Digest Result}
    {q : Nat} (bound : program.BoundedQueries q) (initial : Digest)
    (table : CompressionTable Payload Digest) (good : ForwardFresh initial table) :
    eventProb (program.run RandomOracle.oracle table) (fun out => ¬ForwardFresh initial out.state) ≤
      ((q * (2 * (table.length + q) + 2) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
  RandomOracle.run_avoided_bound bound (graphForbidden initial) 2 2
    (fun earlier input => le_of_eq (graphForbidden_length initial earlier input)) table good

/-- Includes internal hash calls hidden behind high-level queries. With
Q = q*blockLimit, the concrete error is 2Q(Q+1)/card(Digest). This is not yet a
bound on the distinguishing advantage: hidden-chain guesses remain separate. -/
theorem real_forward_failure_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (initial : Digest) (terminal : Payload) :
    eventProb (attack.run (realWorld initial terminal) [])
      (fun out => ¬ForwardFresh initial out.state) ≤
      ((2 * (q * blockLimit) * (q * blockLimit + 1) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have he := congrArg (fun p : ProbComp (CompressionTable Payload Digest × Result) =>
    eventProb p (fun answer => ¬ForwardFresh initial answer.1))
    (expand_run initial terminal attack [])
  simp only [eventProb_map, Program.resultState] at he
  rw [← he]
  have hb := run_forward_failure_bound (bound.expanded_queries initial terminal) initial []
    (by trivial)
  simpa only [List.length_nil, Nat.zero_add,
    show (q * blockLimit) * (2 * (q * blockLimit) + 2) =
      2 * (q * blockLimit) * (q * blockLimit + 1) by ring] using hb

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- A new data edge whose output avoids all earlier input chaining values
cannot create a new chain ending at a different output. This rules out
retroactively completing an old terminal query by sampling its missing prefix. -/
theorem DataChain.remove_new_edge {initial : Digest} {table : CompressionTable Payload Digest}
    {newInput : CompressionInput Payload Digest} {newOutput target : Digest}
    {blocks : List Payload}
    (avoids : newOutput ∉ table.map (fun entry => entry.1.1))
    (chain : DataChain initial ((newInput, newOutput) :: table) blocks target)
    (different : target ≠ newOutput) : DataChain initial table blocks target := by
  induction chain with
  | nil => exact .nil
  | @snoc blocks previous target block chain edge ih =>
      rcases List.mem_cons.mp edge with he | he
      · exact False.elim (different (congrArg Prod.snd he))
      · apply DataChain.snoc block (ih ?_) he
        intro eq
        exact avoids (List.mem_map.mpr ⟨((previous, (false, block)), target), he, eq⟩)

/-- A low-level terminal query on a complete private chain forwards exactly
the corresponding message to the ideal oracle. No ideal state is inspected. -/
theorem simulator_complete_chain {IdealState : Type}
    (ideal : Oracle (List Payload) Digest IdealState) (initial : Digest) (terminal : Payload)
    (table : CompressionTable Payload Digest) (state : IdealState)
    (blocks : List Payload) (target : Digest)
    (good : ForwardFresh initial table) (chain : DataChain initial table blocks target)
    (fresh : table.lookup (target, (true, terminal)) = none) :
    compressionSimulator ideal initial terminal (table, state) (target, (true, terminal)) =
      (ideal state blocks).map (fun answer =>
        ((((target, (true, terminal)), answer.2) :: table, answer.1), answer.2)) := by
  obtain ⟨injective, avoid⟩ := freshOutputs_graph good.outputs
  have found := messagePrefix_complete injective avoid chain
  rw [compressionSimulator_eq]
  simp only [fresh, found, ↓reduceIte, and_self]

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- An older input cannot acquire a new data prefix when one fresh entry is
prepended to the table. This is a chronological statement, not a claim that
hidden chains are already known to the simulator. -/
theorem no_late_chain {initial : Digest} {table : CompressionTable Payload Digest}
    {newInput oldInput : CompressionInput Payload Digest} {newOutput oldOutput : Digest}
    {blocks : List Payload}
    (good : ForwardFresh initial ((newInput, newOutput) :: table))
    (old : (oldInput, oldOutput) ∈ table)
    (chain : DataChain initial ((newInput, newOutput) :: table) blocks oldInput.1) :
    DataChain initial table blocks oldInput.1 := by
  apply chain.remove_new_edge
  · intro hm
    exact good.1 (by
      simp only [graphForbidden, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (Or.inr hm)))
  · intro he
    exact good.1 (by
      simp only [graphForbidden, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨(oldInput, oldOutput), old, he⟩))))

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- The no-late-completion invariant persists across any number of subsequent
samples, using the actual chronological order of the final table. -/
theorem no_late_chain_append {initial : Digest}
    (later table : CompressionTable Payload Digest)
    (oldInput : CompressionInput Payload Digest) (oldOutput : Digest)
    (old : (oldInput, oldOutput) ∈ table)
    (good : ForwardFresh initial (later ++ table))
    {blocks : List Payload} (chain : DataChain initial (later ++ table) blocks oldInput.1) :
    DataChain initial table blocks oldInput.1 := by
  induction later with
  | nil => exact chain
  | cons entry later ih =>
      apply ih good.2
      exact no_late_chain good (List.mem_append_right later old) chain


omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- A later good edge cannot create a new data path to an older output. -/
theorem DataChain.old_output {initial : Digest}
    {table : CompressionTable Payload Digest} {newInput : CompressionInput Payload Digest}
    {newOutput : Digest} {old : CompressionInput Payload Digest × Digest}
    (good : ForwardFresh initial ((newInput, newOutput) :: table)) (entry : old ∈ table)
    {blocks : List Payload} (chain : DataChain initial ((newInput, newOutput) :: table) blocks old.2) :
    DataChain initial table blocks old.2 := by
  apply chain.remove_new_edge
  · intro hm
    exact good.1 (by
      simp only [graphForbidden, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (Or.inr hm)))
  · intro he
    exact good.1 (by
      simp only [graphForbidden, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨old, entry, he⟩))))

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Arbitrarily many later good edges cannot make an older output newly reachable. -/
theorem DataChain.old_output_append {initial : Digest}
    {table : CompressionTable Payload Digest} (later : CompressionTable Payload Digest)
    {old : CompressionInput Payload Digest × Digest}
    (good : ForwardFresh initial (later ++ table)) (entry : old ∈ table)
    {blocks : List Payload} (chain : DataChain initial (later ++ table) blocks old.2) :
    DataChain initial table blocks old.2 := by
  induction later with
  | nil => exact chain
  | cons newEntry later ih =>
      exact ih good.2 (chain.old_output good (List.mem_append_right _ entry))


/-- Public exposure order differs from full sampling order. A terminal value
may already have been returned by the ideal hash, so terminal entries need only
avoid output collisions and the initial value. Data entries additionally avoid
older input states, because only data edges can create a new chain prefix. -/
def dataGraphForbidden (initial : Digest) (table : CompressionTable Payload Digest)
    (input : CompressionInput Payload Digest) : List Digest :=
  if input.2.1 then initial :: table.map Prod.snd else graphForbidden initial table input

/-- Graph condition appropriate to the simulator's public exposure order. -/
def DataForwardFresh (initial : Digest) (table : CompressionTable Payload Digest) : Prop :=
  RandomOracle.Avoided (dataGraphForbidden initial) table

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem ForwardFresh.data {initial : Digest} {table : CompressionTable Payload Digest}
    (good : ForwardFresh initial table) : DataForwardFresh initial table := by
  apply RandomOracle.Avoided.mono (large := graphForbidden initial) _ good
  intro earlier input value hm
  cases marker : input.2.1 <;>
    simp only [dataGraphForbidden, marker, Bool.false_eq_true, ↓reduceIte] at hm
  · exact hm
  · simp only [graphForbidden, List.mem_cons, List.mem_append] at *
    tauto

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
theorem DataForwardFresh.outputs {initial : Digest} {table : CompressionTable Payload Digest}
    (good : DataForwardFresh initial table) : RandomOracle.FreshOutputs initial table := by
  rw [RandomOracle.freshOutputs_iff_avoided]
  apply RandomOracle.Avoided.mono (large := dataGraphForbidden initial) _ good
  intro earlier input value hm
  cases marker : input.2.1 <;>
    simp only [dataGraphForbidden, marker, Bool.false_eq_true, ↓reduceIte]
  · simp only [graphForbidden, List.mem_cons, List.mem_append] at *
    tauto
  · exact hm

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Adding a terminal edge never creates a data path, regardless of its output. -/
theorem DataChain.remove_terminal {initial : Digest} {table : CompressionTable Payload Digest}
    {newInput : CompressionInput Payload Digest} {newOutput target : Digest}
    {blocks : List Payload} (terminal : newInput.2.1 = true)
    (chain : DataChain initial ((newInput, newOutput) :: table) blocks target) :
    DataChain initial table blocks target := by
  induction chain with
  | nil => exact .nil
  | snoc block chain edge ih =>
      rcases List.mem_cons.mp edge with he | he
      · have marker := congrArg (fun entry : CompressionInput Payload Digest × Digest => entry.1.2.1) he
        simp only [terminal] at marker
        cases marker
      · exact .snoc block ih he

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Only a new data edge can retroactively complete an older input. Terminal
outputs need no avoidance condition on old input states for this lemma. -/
theorem data_no_late_chain {initial : Digest} {table : CompressionTable Payload Digest}
    {newInput oldInput : CompressionInput Payload Digest} {newOutput oldOutput : Digest}
    {blocks : List Payload}
    (good : DataForwardFresh initial ((newInput, newOutput) :: table))
    (old : (oldInput, oldOutput) ∈ table)
    (chain : DataChain initial ((newInput, newOutput) :: table) blocks oldInput.1) :
    DataChain initial table blocks oldInput.1 := by
  cases marker : newInput.2.1 with
  | true => exact chain.remove_terminal marker
  | false =>
      have avoids := good.1
      simp only [dataGraphForbidden, marker, Bool.false_eq_true, ↓reduceIte] at avoids
      apply chain.remove_new_edge
      · intro hm
        exact avoids (by
          simp only [graphForbidden, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr (Or.inr hm)))
      · intro he
        exact avoids (by
          simp only [graphForbidden, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨(oldInput, oldOutput), old, he⟩))))

end Foundation.Hash
