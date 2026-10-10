import Foundation.Constructions.Hash.ExecutionChains
import Foundation.Constructions.Hash.SimulatorInvariant
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! An instrumented real experiment. Only public compression calls add to the
public table; internal hash evaluations update the shared compression table.
The extra records are hidden proof state. Projection preserves the complete
public outcome, and does not assume that hidden intermediate values are fresh.
This is the first real-game instrumentation in CSF 2012, Section V, specialized
to the marker-terminal encoding; no external proof code is copied. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Result : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

local instance : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance trackedListBEq : BEq (List Payload) := instBEqOfDecidableEq

structure TrackedRealState (Payload Digest : Type) where
  full : CompressionTable Payload Digest
  exposed : CompressionTable Payload Digest
  hashes : RandomOracle.Table (List Payload) Digest
  guessed : Bool

/-- Empty shared/public graphs, completed-message cache, and failure flag. -/
def TrackedRealState.empty : TrackedRealState Payload Digest := ⟨[], [], [], false⟩

/-- Public inputs are stored once, as in the candidate simulator. This record
is separate from the shared table used by actual compression evaluations. -/
def rememberPublic (table : CompressionTable Payload Digest)
    (input : CompressionInput Payload Digest) (output : Digest) :
    CompressionTable Payload Digest :=
  match table.lookup input with
  | some _ => table
  | none => (input, output) :: table

/-- Store a completed hash message once, matching lazy ideal-hash storage. -/
def rememberHash (table : RandomOracle.Table (List Payload) Digest)
    (message : List Payload) (output : Digest) : RandomOracle.Table (List Payload) Digest :=
  match table.lookup message with
  | some _ => table
  | none => (message, output) :: table

/-- Only a new public terminal call can register a low-level completed message.
The recognition procedure is exactly the one used by the candidate simulator. -/
def recordLowHash (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (input : CompressionInput Payload Digest)
    (output : Digest) : RandomOracle.Table (List Payload) Digest :=
  if state.exposed.lookup input = none then
    match terminalMessage initial terminal state.exposed input with
    | some message => rememberHash state.hashes message output
    | none => state.hashes
  else state.hashes

/-- Outputs of data edges which have not been exposed by the compression
interface. Terminal outputs are excluded, as they may have been returned by
high-level hash calls. Membership is evaluated only by proof instrumentation. -/
def hiddenDataOutputs (state : TrackedRealState Payload Digest) : List Digest :=
  state.full.filterMap (fun entry =>
    if entry.1.2.1 = false ∧ entry ∉ state.exposed then some entry.2 else none)

/-- Only a previously unexposed compression input can introduce a new guess
failure. The flag is monotone and is not returned to the adversary. -/
def markHiddenGuess (state : TrackedRealState Payload Digest)
    (input : CompressionInput Payload Digest) : Bool :=
  if state.exposed.lookup input = none then
    state.guessed || decide (input.1 ∈ hiddenDataOutputs state)
  else state.guessed

noncomputable def trackedRealWorld (initial : Digest) (terminal : Payload) :
    Oracle (WorldInput Payload Digest) Digest (TrackedRealState Payload Digest) :=
  fun state request => match request with
  | .inl message =>
      ((prefixFreeMD initial terminal message).run RandomOracle.oracle state.full).map
        (fun out => (⟨out.state, state.exposed, rememberHash state.hashes message out.result, state.guessed⟩, out.result))
  | .inr input =>
      (RandomOracle.oracle state.full input).map (fun answer =>
        (⟨answer.1, rememberPublic state.exposed input answer.2, recordLowHash initial terminal state input answer.2, markHiddenGuess state input⟩, answer.2))

/-- All public entries denote the actual value in the shared compression table.
No condition on the chronology of public versus hidden evaluations is imposed. -/
def PublicConsistent (state : TrackedRealState Payload Digest) : Prop :=
  ∀ entry ∈ state.exposed, state.full.lookup entry.1 = some entry.2

/-- Forgetting the proof records yields the real oracle's exact transition. -/
theorem trackedRealWorld_project (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (request : WorldInput Payload Digest) :
    (trackedRealWorld initial terminal state request).map
      (fun answer => (answer.1.full, answer.2)) =
      realWorld initial terminal state.full request := by
  cases request with
  | inl message =>
      simp only [trackedRealWorld, realWorld, PMF.map_comp, Function.comp_def]
  | inr input =>
      simp only [trackedRealWorld, realWorld, PMF.map_comp, Function.comp_def]
      exact PMF.map_id _

/-- Results, full compression state, and the entire public trace are preserved
for arbitrary adaptive adversaries, including their local coin choices. -/
theorem trackedReal_run (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest) :
    (attack.run (trackedRealWorld initial terminal) state).map
      (Program.mapState TrackedRealState.full) =
      attack.run (realWorld initial terminal) state.full :=
  Program.run_state_map TrackedRealState.full _ _
    (trackedRealWorld_project initial terminal) attack state

/-- The intermediate experiment changes no distinguishing probability. -/
theorem trackedReal_event (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest)
    (event : Outcome (WorldInput Payload Digest) Digest Result
      (CompressionTable Payload Digest) → Prop) :
    eventProb (attack.run (trackedRealWorld initial terminal) state)
      (fun out => event (Program.mapState TrackedRealState.full out)) =
      eventProb (attack.run (realWorld initial terminal) state.full) event := by
  rw [← eventProb_map, trackedReal_run]

omit [Fintype Digest] [Nonempty Digest] in
theorem PublicConsistent.public_subset {state : TrackedRealState Payload Digest}
    (consistent : PublicConsistent state) : state.exposed ⊆ state.full := by
  intro entry hm
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp (consistent entry hm)
  rw [he]
  exact List.mem_append_right _ (List.mem_cons_self ..)

/-- Every actual hash evaluation retains all previously exposed values, and
an actual low-level response records the value returned by shared compression. -/
theorem trackedReal_step_consistent (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (consistent : PublicConsistent state)
    (request : WorldInput Payload Digest)
    (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal state request).support) :
    PublicConsistent answer.1 := by
  cases request with
  | inl message =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, ho, rfl⟩ := support
      intro entry hm
      exact (RandomOracle.run (prefixFreeMD initial terminal message) state.full out ho).1
        entry.1 entry.2 (consistent entry hm)
  | inr input =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, hr, rfl⟩ := support
      obtain ⟨records, keeps, _⟩ := RandomOracle.step state.full input response hr
      intro entry hm
      cases hp : state.exposed.lookup input with
      | some value =>
          simp only [rememberPublic, hp] at hm
          exact keeps entry.1 entry.2 (consistent entry hm)
      | none =>
          simp only [rememberPublic, hp, List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact records
          · exact keeps entry.1 entry.2 (consistent entry hm)

/-- Previously exposed compression inputs are answered exactly as in the
simulator's known-input branch, even if high-level calls occur between them. -/
theorem trackedReal_low_known (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (consistent : PublicConsistent state)
    (input : CompressionInput Payload Digest) (output : Digest)
    (known : state.exposed.lookup input = some output) :
    trackedRealWorld initial terminal state (.inr input) = PMF.pure (state, output) := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp known
  have hm : (input, output) ∈ state.exposed := by rw [he]; simp
  have full := consistent (input, output) hm
  simp only [trackedRealWorld, RandomOracle.known state.full input output full,
    PMF.pure_map, rememberPublic, recordLowHash, markHiddenGuess, known, Option.some_ne_none, ↓reduceIte]

/-- Public/shared consistency holds throughout the full adaptive interaction. -/
theorem trackedReal_run_consistent (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest) (consistent : PublicConsistent state)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) state).support) :
    PublicConsistent out.state := by
  induction attack generalizing state out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact consistent
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state consistent out ht
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      exact ih answer.2 answer.1
        (trackedReal_step_consistent initial terminal state consistent request answer ha) tail ht


/-- Outputs of exposed edges can only be reached by exposed data paths. This
is stronger than shared/public agreement and needs the hidden-guess condition. -/
def ExposedPaths (initial : Digest) (state : TrackedRealState Payload Digest) : Prop :=
  ∀ blocks target, DataChain initial state.full blocks target →
    ∀ entry ∈ state.exposed, entry.2 = target → DataChain initial state.exposed blocks target

omit [Fintype Digest] [Nonempty Digest] in
theorem rememberPublic_includes (table : CompressionTable Payload Digest)
    (input : CompressionInput Payload Digest) (output : Digest) :
    table ⊆ rememberPublic table input output := by
  cases ht : table.lookup input with
  | some value =>
      simp only [rememberPublic, ht]
      exact List.Subset.refl _
  | none =>
      simp only [rememberPublic, ht]
      exact fun _ hm => List.mem_cons_of_mem _ hm

omit [Fintype Digest] [Nonempty Digest] in
/-- A reachable data endpoint which is not hidden has a wholly exposed path. -/
theorem ExposedPaths.not_hidden {initial : Digest} {state : TrackedRealState Payload Digest}
    (paths : ExposedPaths initial state) {blocks : List Payload} {target : Digest}
    (chain : DataChain initial state.full blocks target)
    (visible : target ∉ hiddenDataOutputs state) :
    DataChain initial state.exposed blocks target := by
  cases chain with
  | nil => exact .nil
  | @snoc blocks previous target block chain edge =>
      have exposed : ((previous, (false, block)), target) ∈ state.exposed := by
        by_contra missing
        apply visible
        apply List.mem_filterMap.mpr
        exact ⟨((previous, (false, block)), target), edge, by simp [missing]⟩
      exact paths (blocks ++ [block]) target (.snoc block chain edge) _ exposed rfl

theorem trackedReal_step_full_extends (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (request : WorldInput Payload Digest)
    (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal state request).support) :
    ∃ later : CompressionTable Payload Digest, answer.1.full = later ++ state.full := by
  cases request with
  | inl message =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, ho, rfl⟩ := support
      exact RandomOracle.run_table_extends (prefixFreeMD initial terminal message) state.full out ho
  | inr input =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, hr, rfl⟩ := support
      exact RandomOracle.step_table_extends state.full input response hr

/-- Outside chronological graph failure and the recorded hidden guesses,
exposed paths are preserved by the actual real-world transition. -/
theorem trackedReal_step_paths (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (consistent : PublicConsistent state)
    (paths : ExposedPaths initial state) (request : WorldInput Payload Digest)
    (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal state request).support)
    (good : ForwardFresh initial answer.1.full) (noGuess : answer.1.guessed = false) :
    ExposedPaths initial answer.1 := by
  cases request with
  | inl message =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, ho, rfl⟩ := support
      obtain ⟨later, he⟩ := RandomOracle.run_table_extends
        (prefixFreeMD initial terminal message) state.full out ho
      intro blocks target chain entry exposed endpoint
      have old := consistent.public_subset exposed
      rw [he] at chain good
      rw [← endpoint] at chain
      exact paths blocks target (by
        rw [← endpoint]
        exact chain.old_output_append later good old) entry exposed endpoint
  | inr input =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, hr, rfl⟩ := support
      obtain ⟨later, he⟩ := RandomOracle.step_table_extends state.full input response hr
      intro blocks target chain entry exposed endpoint
      have oldEntry (entry : CompressionInput Payload Digest × Digest)
          (hm : entry ∈ state.exposed) (hc : DataChain initial response.1 blocks target)
          (endpoint : entry.2 = target) :
          DataChain initial (rememberPublic state.exposed input response.2) blocks target := by
        have old := consistent.public_subset hm
        rw [he, ← endpoint] at hc
        have hg : ForwardFresh initial (later ++ state.full) := by simpa only [← he] using good
        have before := hc.old_output_append later hg old
        have publicPath := paths blocks target (by simpa only [endpoint] using before) entry hm endpoint
        exact publicPath.mono (rememberPublic_includes state.exposed input response.2)
      cases hp : state.exposed.lookup input with
      | some value =>
          simp only [rememberPublic, hp] at exposed
          exact oldEntry entry exposed chain endpoint
      | none =>
          simp only [rememberPublic, hp, List.mem_cons] at exposed
          rcases exposed with rfl | exposed
          · simp only at endpoint
            subst target
            cases chain with
            | nil => exact .nil
            | @snoc blocks previous target block prior lastEdge =>
                obtain ⟨injective, _⟩ := freshOutputs_graph good.outputs
                have records := (RandomOracle.step state.full input response hr).1
                obtain ⟨before, after, ht, _⟩ := List.lookup_eq_some_iff.mp records
                have returned : (input, response.2) ∈ response.1 := by rw [ht]; simp
                have same := injective _ lastEdge _ returned rfl
                have hi : input = (previous, (false, block)) := same.symm
                subst input
                have beforePath := compression_step_chain_input initial state.full
                  (previous, (false, block)) response hr good prior
                have hflag : (state.guessed || decide (previous ∈ hiddenDataOutputs state)) = false := by
                  simpa only [markHiddenGuess, hp, ↓reduceIte] using noGuess
                have visible : previous ∉ hiddenDataOutputs state := by
                  simpa only [decide_eq_false_iff_not] using (Bool.or_eq_false_iff.mp hflag).2
                have publicPath := paths.not_hidden beforePath visible
                apply DataChain.snoc block
                  (publicPath.mono (rememberPublic_includes state.exposed _ response.2))
                simp only [rememberPublic, hp]
                exact List.mem_cons_self ..
          · exact oldEntry entry exposed chain endpoint


theorem trackedReal_step_no_guess (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (request : WorldInput Payload Digest)
    (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal state request).support)
    (noGuess : answer.1.guessed = false) : state.guessed = false := by
  cases request with
  | inl message =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, _, rfl⟩ := support
      exact noGuess
  | inr input =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, _, rfl⟩ := support
      by_cases hp : state.exposed.lookup input = none
      · have hflag : (state.guessed || decide (input.1 ∈ hiddenDataOutputs state)) = false := by
          simpa only [markHiddenGuess, hp, ↓reduceIte] using noGuess
        exact (Bool.or_eq_false_iff.mp hflag).1
      · simpa only [markHiddenGuess, hp, ↓reduceIte] using noGuess

theorem trackedReal_run_full_extends (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) state).support) :
    ∃ later : CompressionTable Payload Digest, out.state.full = later ++ state.full := by
  induction attack generalizing state out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact ⟨[], rfl⟩
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state out ht
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      obtain ⟨added, he⟩ := trackedReal_step_full_extends initial terminal state request answer ha
      obtain ⟨later, hl⟩ := ih answer.2 answer.1 tail ht
      exact ⟨later ++ added, by simp only; rw [hl, he, List.append_assoc]⟩

/-- A false final failure flag certifies no earlier flagged guess. -/
theorem trackedReal_run_no_guess (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) state).support)
    (noGuess : out.state.guessed = false) : state.guessed = false := by
  induction attack generalizing state out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact noGuess
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state out ht noGuess
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      exact trackedReal_step_no_guess initial terminal state request answer ha
        (ih answer.2 answer.1 tail ht noGuess)

/-- The complete adaptive real interaction maintains exposed paths whenever
neither chronological graph failure nor a hidden-state guess has occurred. -/
theorem trackedReal_run_paths (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest) (consistent : PublicConsistent state)
    (paths : ExposedPaths initial state)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) state).support)
    (good : ForwardFresh initial out.state.full) (noGuess : out.state.guessed = false) :
    ExposedPaths initial out.state := by
  induction attack generalizing state out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact paths
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state consistent paths out ht good noGuess
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      obtain ⟨later, he⟩ := trackedReal_run_full_extends initial terminal
        (next answer.2) answer.1 tail ht
      have goodStep : ForwardFresh initial answer.1.full := by
        apply RandomOracle.Avoided.append_tail later answer.1.full
        rw [← he]
        exact good
      have noGuessStep := trackedReal_run_no_guess initial terminal
        (next answer.2) answer.1 tail ht noGuess
      exact ih answer.2 answer.1
        (trackedReal_step_consistent initial terminal state consistent request answer ha)
        (trackedReal_step_paths initial terminal state consistent paths request answer ha goodStep noGuessStep)
        tail ht good noGuess

omit [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- The completed-message cache adds only the supplied message and response. -/
theorem rememberHash_entries (table : RandomOracle.Table (List Payload) Digest)
    (message : List Payload) (output : Digest) :
    rememberHash table message output ⊆ (message, output) :: table := by
  cases h : table.lookup message <;> simp only [rememberHash, h]
  · exact List.Subset.refl _
  · exact fun _ hm => List.mem_cons_of_mem _ hm

omit [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Registering a completed message preserves all previously stored values. -/
theorem rememberHash_keeps (table : RandomOracle.Table (List Payload) Digest)
    (message : List Payload) (output : Digest) (oldMessage : List Payload) (oldOutput : Digest)
    (known : table.lookup oldMessage = some oldOutput) :
    (rememberHash table message output).lookup oldMessage = some oldOutput := by
  cases fresh : table.lookup message with
  | some recorded => simpa only [rememberHash, fresh] using known
  | none =>
      have different : oldMessage ≠ message := by
        intro same
        rw [same, fresh] at known
        cases known
      simp [rememberHash, fresh, List.lookup_cons, beq_eq_false_iff_ne.mpr different, known]

omit [Fintype Digest] [Nonempty Digest] in
/-- Low-level registration never changes a previously registered hash value. -/
theorem recordLowHash_keeps (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (input : CompressionInput Payload Digest)
    (output : Digest) (message : List Payload) (recorded : Digest)
    (known : state.hashes.lookup message = some recorded) :
    (recordLowHash initial terminal state input output).lookup message = some recorded := by
  unfold recordLowHash
  split
  · split
    · exact rememberHash_keeps state.hashes _ output message recorded known
    · exact known
  · exact known

omit [Fintype Digest] [Nonempty Digest] in
/-- Every new low-level record is recognized by the actual simulator search. -/
theorem recordLowHash_entries (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (input : CompressionInput Payload Digest)
    (output : Digest) (entry : List Payload × Digest)
    (member : entry ∈ recordLowHash initial terminal state input output) :
    entry ∈ state.hashes ∨ ∃ message, entry = (message, output) ∧
      terminalMessage initial terminal state.exposed input = some message := by
  unfold recordLowHash at member
  split at member
  · split at member
    · rename_i message recognized
      rcases List.mem_cons.mp (rememberHash_entries state.hashes message output member) with he | hm
      · exact Or.inr ⟨message, he, recognized⟩
      · exact Or.inl hm
    · exact Or.inl member
  · exact Or.inl member

/-- Every recorded hash response, from either interface, is backed by a
completed path in shared compression. The converse is a separate invariant. -/
def CompletedPaths (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) : Prop :=
  ∀ entry ∈ state.hashes, ∃ target, DataChain initial state.full entry.1 target ∧
    ((target, (true, terminal)), entry.2) ∈ state.full

theorem trackedReal_step_completed (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (publicConsistent : PublicConsistent state)
    (completed : CompletedPaths initial terminal state)
    (request : WorldInput Payload Digest) (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal state request).support) :
    CompletedPaths initial terminal answer.1 := by
  cases request with
  | inl message =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, ho, rfl⟩ := support
      have includes := RandomOracle.run_table_subset (prefixFreeMD initial terminal message) state.full out ho
      intro entry hm
      rcases List.mem_cons.mp (rememberHash_entries state.hashes message out.result hm) with rfl | hm
      · exact prefixFreeMD_chain initial terminal message state.full out ho
      · obtain ⟨target, path, terminalEdge⟩ := completed entry hm
        exact ⟨target, path.mono includes, includes terminalEdge⟩
  | inr input =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, hr, rfl⟩ := support
      have includes := RandomOracle.step_table_subset state.full input response hr
      intro entry hm
      rcases recordLowHash_entries initial terminal state input response.2 entry hm with old | fresh
      · obtain ⟨target, path, terminalEdge⟩ := completed entry old
        exact ⟨target, path.mono includes, includes terminalEdge⟩
      · obtain ⟨message, rfl, recognized⟩ := fresh
        obtain ⟨marked, chain⟩ := terminalMessage_sound initial terminal state.exposed input message recognized
        refine ⟨input.1, (chain.mono publicConsistent.public_subset).mono includes, ?_⟩
        have records := (RandomOracle.step state.full input response hr).1
        obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp records
        rw [he, ← marked]
        simp

theorem trackedReal_run_completed (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest) (publicConsistent : PublicConsistent state)
    (completed : CompletedPaths initial terminal state)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) state).support) :
    CompletedPaths initial terminal out.state := by
  induction attack generalizing state out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact completed
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state publicConsistent completed out ht
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      exact ih answer.2 answer.1
        (trackedReal_step_consistent initial terminal state publicConsistent request answer ha)
        (trackedReal_step_completed initial terminal state publicConsistent completed request answer ha) tail ht

/-- Starting from empty proof records, all three real-game invariants hold.
Only exposed-path reconstruction requires the two failure exclusions. -/
theorem trackedReal_from_empty (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support)
    (good : ForwardFresh initial out.state.full) (noGuess : out.state.guessed = false) :
    PublicConsistent out.state ∧ ExposedPaths initial out.state ∧ CompletedPaths initial terminal out.state := by
  have consistent : PublicConsistent (TrackedRealState.empty (Payload := Payload) (Digest := Digest)) := by
    intro entry hm
    cases hm
  have paths : ExposedPaths initial (TrackedRealState.empty (Payload := Payload)) := by
    intro blocks target chain entry hm
    cases hm
  have completed : CompletedPaths initial terminal (TrackedRealState.empty (Payload := Payload)) := by
    intro entry hm
    cases hm
  exact ⟨trackedReal_run_consistent initial terminal attack _ consistent out support,
    trackedReal_run_paths initial terminal attack _ consistent paths out support good noGuess,
    trackedReal_run_completed initial terminal attack _ consistent completed out support⟩


/-- Every nonhidden reachable endpoint is reconstructed by the simulator's
actual bounded search on the exposed table. -/
def PublicReconstructible (initial : Digest) (state : TrackedRealState Payload Digest) : Prop :=
  ∀ blocks target, DataChain initial state.full blocks target →
    target ∉ hiddenDataOutputs state →
    messagePrefix initial state.exposed state.exposed.length target = some blocks

theorem trackedReal_public_search (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support)
    (good : ForwardFresh initial out.state.full) (noGuess : out.state.guessed = false) :
    PublicReconstructible initial out.state := by
  obtain ⟨consistent, paths, _⟩ := trackedReal_from_empty initial terminal attack out support good noGuess
  obtain ⟨injective, avoid⟩ := freshOutputs_graph good.outputs
  have includes := consistent.public_subset
  have publicInjective : OutputInjective out.state.exposed := by
    intro left hl right hr same
    exact injective left (includes hl) right (includes hr) same
  have publicAvoid : AvoidInitial initial out.state.exposed := by
    intro entry hm
    exact avoid entry (includes hm)
  intro blocks target chain visible
  exact messagePrefix_complete publicInjective publicAvoid (paths.not_hidden chain visible)

/-- Any empty-start real invariant proved under the two failure exclusions
inherits the same failure bound. The actual hidden-guess probability remains an
explicit unresolved term, not an additional security assumption. -/
theorem trackedReal_invariant_failure_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (initial : Digest) (terminal : Payload)
    (invariant : TrackedRealState Payload Digest → Prop)
    (holds : ∀ out ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support,
      ForwardFresh initial out.state.full → out.state.guessed = false → invariant out.state) :
    eventProb (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty)
      (fun out => ¬invariant out.state) ≤
      (((2 * (q * blockLimit) * (q * blockLimit + 1)) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      eventProb (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty)
        (fun out => out.state.guessed = true) := by
  classical
  have graph : eventProb (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty)
      (fun out => ¬ForwardFresh initial out.state.full) ≤
      (((2 * (q * blockLimit) * (q * blockLimit + 1)) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    have he := trackedReal_event initial terminal attack TrackedRealState.empty
      (fun out => ¬ForwardFresh initial out.state)
    simp only [Program.mapState, TrackedRealState.empty] at he
    simpa only [TrackedRealState.empty] using
      he.le.trans (real_forward_failure_bound bound initial terminal)
  calc
    _ ≤ eventProb (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty)
        (fun out => ¬ForwardFresh initial out.state.full ∨ out.state.guessed = true) := by
      apply eventProb_mono_of_support
      intro out support fails
      by_cases good : ForwardFresh initial out.state.full
      · by_cases guessed : out.state.guessed = true
        · exact Or.inr guessed
        · exact False.elim (fails (holds out support good (Bool.eq_false_iff.mpr guessed)))
      · exact Or.inl good
    _ ≤ _ := eventProb_or_le _ _ _
    _ ≤ _ := add_le_add graph (le_refl _)


/-- The unexplained part of public reconstruction failure is isolated as the
actual hidden-guess flag of the instrumented real game. Its probability is not
assumed small here, and the bound is not an indifferentiability theorem. -/
theorem trackedReal_reconstruction_failure_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (initial : Digest) (terminal : Payload) :
    eventProb (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty)
      (fun out => ¬PublicReconstructible initial out.state) ≤
      (((2 * (q * blockLimit) * (q * blockLimit + 1)) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      eventProb (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty)
        (fun out => out.state.guessed = true) := by
  exact trackedReal_invariant_failure_bound bound initial terminal (PublicReconstructible initial)
    (trackedReal_public_search initial terminal attack)

/-- The instrumented real world retains functional shared storage. This is
unconditional on all collision and hidden-guess exclusions. -/
theorem trackedReal_step_table_consistent (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (consistent : RandomOracle.TableConsistent state.full)
    (request : WorldInput Payload Digest) (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal state request).support) :
    RandomOracle.TableConsistent answer.1.full := by
  cases request with
  | inl message =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, ho, rfl⟩ := support
      exact RandomOracle.run_table_consistent (prefixFreeMD initial terminal message) state.full consistent out ho
  | inr input =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, hr, rfl⟩ := support
      exact RandomOracle.step_table_consistent state.full consistent input response hr

/-- Functional shared storage holds after the complete adaptive interaction. -/
theorem trackedReal_run_table_consistent (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest) (consistent : RandomOracle.TableConsistent state.full)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) state).support) :
    RandomOracle.TableConsistent out.state.full := by
  induction attack generalizing state out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact consistent
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state consistent out ht
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      exact ih answer.2 answer.1
        (trackedReal_step_table_consistent initial terminal state consistent request answer ha) tail ht

omit [Fintype Digest] [Nonempty Digest] in
/-- Every log of genuine completed paths is itself a coherent hash table.
The result permits repeated messages and compression-output collisions. -/
theorem CompletedPaths.hashes_consistent {initial : Digest} {terminal : Payload}
    {state : TrackedRealState Payload Digest}
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full) :
    RandomOracle.TableConsistent state.hashes := by
  apply RandomOracle.TableConsistent.of_functional
  intro message left right hl hr
  obtain ⟨leftTarget, leftChain, leftEdge⟩ := completed (message, left) hl
  obtain ⟨rightTarget, rightChain, rightEdge⟩ := completed (message, right) hr
  have same := leftChain.forward_unique consistent rightChain
  subst rightTarget
  exact consistent.functional leftEdge rightEdge

/-- Real high-level response logs are coherent after any adaptive empty-start
interaction, without imposing the good-graph or no-guess conditions. -/
theorem trackedReal_hashes_consistent (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support) :
    RandomOracle.TableConsistent out.state.hashes := by
  have full := trackedReal_run_table_consistent initial terminal attack TrackedRealState.empty
    (by intro entry hm; cases hm) out support
  have completed := trackedReal_run_completed initial terminal attack TrackedRealState.empty
    (by intro entry hm; cases hm) (by intro entry hm; cases hm) out support
  exact completed.hashes_consistent full

omit [Fintype Digest] [Nonempty Digest] in
/-- Any other completed path for a logged message yields its recorded value.
This relates forward functional evaluation to a backwards simulator search. -/
theorem CompletedPaths.terminal_agrees {initial : Digest} {terminal : Payload}
    {state : TrackedRealState Payload Digest}
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    {message : List Payload} {target output recorded : Digest}
    (known : state.hashes.lookup message = some recorded)
    (chain : DataChain initial state.full message target)
    (terminalEdge : ((target, (true, terminal)), output) ∈ state.full) : output = recorded := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp known
  have member : (message, recorded) ∈ state.hashes := by rw [he]; simp
  obtain ⟨recordedTarget, recordedChain, recordedEdge⟩ := completed _ member
  have same := chain.forward_unique consistent recordedChain
  subst recordedTarget
  exact consistent.functional terminalEdge recordedEdge

/-- A repeated high-level query is deterministic and leaves all instrumented
state unchanged, including the completed-message cache. -/
theorem trackedReal_high_known (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    (message : List Payload) (output : Digest)
    (known : state.hashes.lookup message = some output) :
    trackedRealWorld initial terminal state (.inl message) =
      PMF.pure (state, output) := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp known
  have member : (message, output) ∈ state.hashes := by rw [he]; simp
  obtain ⟨target, chain, terminalEdge⟩ := completed _ member
  obtain ⟨trace, replay⟩ := prefixFreeMD_replay consistent chain terminalEdge
  simp only [trackedRealWorld, replay, PMF.pure_map, rememberHash, known]

/-- When public backward search recovers a previously hashed message, the
actual low-level terminal response is precisely its recorded ideal-hash value.
No new uniform value is drawn, even if this terminal input is newly exposed. -/
theorem trackedReal_terminal_known (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    (publicConsistent : PublicConsistent state)
    (target : Digest) (message : List Payload) (output : Digest)
    (search : messagePrefix initial state.exposed state.exposed.length target = some message)
    (known : state.hashes.lookup message = some output) :
    trackedRealWorld initial terminal state (.inr (target, (true, terminal))) =
      PMF.pure (⟨state.full, rememberPublic state.exposed (target, (true, terminal)) output,
        state.hashes, markHiddenGuess state (target, (true, terminal))⟩, output) := by
  have publicChain := (messagePrefix_sound initial state.exposed _ target message search).1
  have fullChain := publicChain.mono publicConsistent.public_subset
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp known
  have member : (message, output) ∈ state.hashes := by rw [he]; simp
  obtain ⟨recordedTarget, recordedChain, recordedEdge⟩ := completed _ member
  have same := fullChain.forward_unique consistent recordedChain
  subst recordedTarget
  have value := consistent _ recordedEdge
  simp only [trackedRealWorld,
    RandomOracle.known state.full (target, (true, terminal)) output value, PMF.pure_map]
  simp [recordLowHash, terminalMessage, search, rememberHash, known]

/-- On a publicly reconstructed, already hashed message, the real terminal
step and the actual candidate simulator have the same joint exposed-table,
hash-table, and response law. Hidden full-table and flag records are forgotten. -/
theorem trackedReal_terminal_simulator (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    (publicConsistent : PublicConsistent state)
    (target : Digest) (message : List Payload) (output : Digest)
    (search : messagePrefix initial state.exposed state.exposed.length target = some message)
    (known : state.hashes.lookup message = some output) :
    (trackedRealWorld initial terminal state (.inr (target, (true, terminal)))).map
      (fun answer => ((answer.1.exposed, answer.1.hashes), answer.2)) =
    compressionSimulator RandomOracle.oracle initial terminal
      (state.exposed, state.hashes) (target, (true, terminal)) := by
  rw [trackedReal_terminal_known initial terminal state completed consistent publicConsistent
    target message output search known, PMF.pure_map, compressionSimulator_eq]
  cases exposed : state.exposed.lookup (target, (true, terminal)) with
  | none =>
      simp only [List.lookup_eq_findSome?, Bool.beq_eq_decide_eq, decide_eq_true_eq] at exposed
      simp [rememberPublic, List.lookup_eq_findSome?, Bool.beq_eq_decide_eq, exposed, search,
        RandomOracle.known state.hashes message output known, PMF.pure_map]
  | some recorded =>
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp exposed
      have member : ((target, (true, terminal)), recorded) ∈ state.exposed := by rw [he]; simp
      have records := publicConsistent _ member
      obtain ⟨beforeHash, afterHash, hh, _⟩ := List.lookup_eq_some_iff.mp known
      have hashMember : (message, output) ∈ state.hashes := by rw [hh]; simp
      obtain ⟨recordedTarget, chain, edge⟩ := completed _ hashMember
      have publicChain := (messagePrefix_sound initial state.exposed _ target message search).1
      have same := (publicChain.mono publicConsistent.public_subset).forward_unique consistent chain
      subst recordedTarget
      have equality : recorded = output := Option.some.inj (records.symm.trans (consistent _ edge))
      subst recorded
      simp only [List.lookup_eq_findSome?, Bool.beq_eq_decide_eq, decide_eq_true_eq] at exposed
      simp [rememberPublic, List.lookup_eq_findSome?, Bool.beq_eq_decide_eq, exposed]

omit [Fintype Digest] [Nonempty Digest] in
/-- Registering another genuine path gives its actual value, even when that
message was already present. Shared-table functionality prevents a conflict. -/
theorem CompletedPaths.remember_value {initial : Digest} {terminal : Payload}
    {state : TrackedRealState Payload Digest} (completed : CompletedPaths initial terminal state)
    {after : CompressionTable Payload Digest} (includes : state.full ⊆ after)
    (consistent : RandomOracle.TableConsistent after)
    {message : List Payload} {target output : Digest}
    (chain : DataChain initial after message target)
    (terminalEdge : ((target, (true, terminal)), output) ∈ after) :
    (rememberHash state.hashes message output).lookup message = some output := by
  cases known : state.hashes.lookup message with
  | none => simp [rememberHash, known]
  | some recorded =>
      obtain ⟨before, later, he, _⟩ := List.lookup_eq_some_iff.mp known
      have member : (message, recorded) ∈ state.hashes := by rw [he]; simp
      obtain ⟨recordedTarget, recordedChain, recordedEdge⟩ := completed _ member
      have same := chain.forward_unique consistent (recordedChain.mono includes)
      subst recordedTarget
      have outputs : output = recorded := consistent.functional terminalEdge (includes recordedEdge)
      simp [rememberHash, known, outputs]

/-- After a high-level evaluation, every completed terminal in the full graph
is registered. Old terminals cannot acquire new prefixes under the chronological
graph condition, and the only new terminal is the queried message's endpoint. -/
theorem trackedReal_high_terminal (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (covered : TerminalConsistent initial terminal state.full state.hashes)
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    (message : List Payload)
    (out : Outcome (CompressionInput Payload Digest) Digest Digest (CompressionTable Payload Digest))
    (support : out ∈ ((prefixFreeMD initial terminal message).run RandomOracle.oracle state.full).support)
    (good : ForwardFresh initial out.state) :
    TerminalConsistent initial terminal out.state (rememberHash state.hashes message out.result) := by
  have includes := RandomOracle.run_table_subset (prefixFreeMD initial terminal message) state.full out support
  have afterConsistent := RandomOracle.run_table_consistent (prefixFreeMD initial terminal message)
    state.full consistent out support
  obtain ⟨actualTarget, actualChain, actualTerminal, terminals⟩ :=
    prefixFreeMD_terminal_entries initial terminal message state.full out support
  have recorded := completed.remember_value includes afterConsistent actualChain actualTerminal
  obtain ⟨injective, avoid⟩ := freshOutputs_graph good.outputs
  obtain ⟨later, extended⟩ := RandomOracle.run_table_extends
    (prefixFreeMD initial terminal message) state.full out support
  intro blocks target output chain edge
  rcases terminals _ edge rfl with old | same
  · have oldChain : DataChain initial state.full blocks target := by
      rw [extended] at chain good
      exact no_late_chain_append later state.full (target, (true, terminal)) output old good chain
    exact rememberHash_keeps state.hashes message out.result blocks output (covered blocks target output oldChain old)
  · have targetSame : target = actualTarget := congrArg (fun entry => entry.1.1) same
    have outputSame : output = out.result := congrArg Prod.snd same
    subst target
    subst output
    have messages := chain.unique injective avoid actualChain
    subst blocks
    exact recorded

/-- A low-level step also keeps every full completed terminal registered.
For a fresh terminal, the absence of a hidden-state guess exposes its prefix,
so the shared recognition procedure registers its completed message. -/
theorem trackedReal_low_terminal (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (covered : TerminalConsistent initial terminal state.full state.hashes)
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    (publicConsistent : PublicConsistent state) (paths : ExposedPaths initial state)
    (input : CompressionInput Payload Digest) (answer : CompressionTable Payload Digest × Digest)
    (support : answer ∈ (RandomOracle.oracle state.full input).support)
    (good : ForwardFresh initial answer.1) (noGuess : markHiddenGuess state input = false) :
    TerminalConsistent initial terminal answer.1 (recordLowHash initial terminal state input answer.2) := by
  cases cached : state.full.lookup input with
  | some output =>
      rw [RandomOracle.known state.full input output cached, PMF.mem_support_pure_iff] at support
      subst answer
      exact covered.mono_ideal (fun message recorded known =>
        recordLowHash_keeps initial terminal state input output message recorded known)
  | none =>
      rw [RandomOracle.fresh state.full input cached, PMF.mem_support_map_iff] at support
      obtain ⟨output, _, rfl⟩ := support
      have publicFresh : state.exposed.lookup input = none := by
        cases exposed : state.exposed.lookup input with
        | none => rfl
        | some recorded =>
            obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp exposed
            have member : (input, recorded) ∈ state.exposed := by rw [he]; simp
            have records := publicConsistent _ member
            simp only [cached] at records
            cases records
      have visible : input.1 ∉ hiddenDataOutputs state := by
        have flag : (state.guessed || decide (input.1 ∈ hiddenDataOutputs state)) = false := by
          simpa only [markHiddenGuess, publicFresh, ↓reduceIte] using noGuess
        simpa only [decide_eq_false_iff_not] using (Bool.or_eq_false_iff.mp flag).2
      apply TerminalConsistent.extend covered good.data
        (fun message recorded known => recordLowHash_keeps initial terminal state input output message recorded known)
      intro blocks target marked chain
      have publicChain : DataChain initial state.exposed blocks target :=
        paths.not_hidden chain (by simpa only [marked] using visible)
      have beforeGood : ForwardFresh initial state.full := good.2
      obtain ⟨injective, avoid⟩ := freshOutputs_graph beforeGood.outputs
      have publicInjective : OutputInjective state.exposed := by
        intro left hl right hr equal
        exact injective left (publicConsistent.public_subset hl) right (publicConsistent.public_subset hr) equal
      have publicAvoid : AvoidInitial initial state.exposed :=
        fun entry hm => avoid entry (publicConsistent.public_subset hm)
      have search := messagePrefix_complete publicInjective publicAvoid publicChain
      have recognized : terminalMessage initial terminal state.exposed input = some blocks := by
        simp [terminalMessage, marked, search]
      have includes : state.full ⊆ (input, output) :: state.full :=
        fun _ hm => List.mem_cons_of_mem _ hm
      have afterConsistent := consistent.cons input output cached
      have newTerminal : ((target, (true, terminal)), output) ∈ (input, output) :: state.full := by
        simp [marked]
      have recorded := completed.remember_value includes afterConsistent (chain.mono includes) newTerminal
      simpa only [recordLowHash, publicFresh, ↓reduceIte, recognized] using recorded

/-- Both real interfaces preserve complete-terminal coverage under the full
graph and hidden-guess exclusions. All auxiliary premises hold from empty. -/
theorem trackedReal_step_terminal (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (covered : TerminalConsistent initial terminal state.full state.hashes)
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    (publicConsistent : PublicConsistent state) (paths : ExposedPaths initial state)
    (request : WorldInput Payload Digest) (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal state request).support)
    (good : ForwardFresh initial answer.1.full) (noGuess : answer.1.guessed = false) :
    TerminalConsistent initial terminal answer.1.full answer.1.hashes := by
  cases request with
  | inl message =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, ho, rfl⟩ := support
      exact trackedReal_high_terminal initial terminal state covered completed consistent message out ho good
  | inr input =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, hr, rfl⟩ := support
      exact trackedReal_low_terminal initial terminal state covered completed consistent publicConsistent paths
        input response hr good noGuess

/-- Complete-terminal coverage is preserved by an arbitrary adaptive real
interaction, provided the final chronological graph and guess conditions hold. -/
theorem trackedReal_run_terminal (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest)
    (covered : TerminalConsistent initial terminal state.full state.hashes)
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    (publicConsistent : PublicConsistent state) (paths : ExposedPaths initial state)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) state).support)
    (good : ForwardFresh initial out.state.full) (noGuess : out.state.guessed = false) :
    TerminalConsistent initial terminal out.state.full out.state.hashes := by
  induction attack generalizing state out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact covered
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state covered completed consistent publicConsistent paths out ht good noGuess
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      obtain ⟨later, extended⟩ := trackedReal_run_full_extends initial terminal (next answer.2) answer.1 tail ht
      have goodStep : ForwardFresh initial answer.1.full := by
        apply RandomOracle.Avoided.append_tail later answer.1.full
        rw [← extended]
        exact good
      have noGuessStep := trackedReal_run_no_guess initial terminal (next answer.2) answer.1 tail ht noGuess
      exact ih answer.2 answer.1
        (trackedReal_step_terminal initial terminal state covered completed consistent publicConsistent paths
          request answer ha goodStep noGuessStep)
        (trackedReal_step_completed initial terminal state publicConsistent completed request answer ha)
        (trackedReal_step_table_consistent initial terminal state consistent request answer ha)
        (trackedReal_step_consistent initial terminal state publicConsistent request answer ha)
        (trackedReal_step_paths initial terminal state publicConsistent paths request answer ha goodStep noGuessStep)
        tail ht good noGuess

/-- Empty-start real interactions register every completed full terminal,
including those assembled entirely through the public compression interface. -/
theorem trackedReal_terminal_from_empty (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support)
    (good : ForwardFresh initial out.state.full) (noGuess : out.state.guessed = false) :
    TerminalConsistent initial terminal out.state.full out.state.hashes := by
  apply trackedReal_run_terminal initial terminal attack TrackedRealState.empty
    (TerminalConsistent.empty initial terminal [])
    (by intro entry hm; cases hm) (by intro entry hm; cases hm)
    (by intro entry hm; cases hm)
    (by intro blocks target chain entry hm; cases hm) out support good noGuess

/-- The real shared hash record therefore agrees with every publicly complete
terminal as well. The public table may omit internal hash evaluations. -/
theorem trackedReal_exposed_terminal_from_empty (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support)
    (good : ForwardFresh initial out.state.full) (noGuess : out.state.guessed = false) :
    TerminalConsistent initial terminal out.state.exposed out.state.hashes := by
  have covered := trackedReal_terminal_from_empty initial terminal attack out support good noGuess
  have publicConsistent := trackedReal_run_consistent initial terminal attack TrackedRealState.empty
    (by intro entry hm; cases hm) out support
  intro blocks target output chain edge
  exact covered blocks target output (chain.mono publicConsistent.public_subset) (publicConsistent.public_subset edge)

/-- All missing real completed-terminal registrations are covered by the
same chronological graph failure or actual hidden-guess event. -/
theorem trackedReal_terminal_failure_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (initial : Digest) (terminal : Payload) :
    eventProb (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty)
      (fun out => ¬TerminalConsistent initial terminal out.state.full out.state.hashes) ≤
      (((2 * (q * blockLimit) * (q * blockLimit + 1)) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      eventProb (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty)
        (fun out => out.state.guessed = true) :=
  trackedReal_invariant_failure_bound bound initial terminal
    (fun state => TerminalConsistent initial terminal state.full state.hashes)
    (trackedReal_terminal_from_empty initial terminal attack)

/-- A message missing from a covering hash record has a fresh terminal input
after its data-prefix execution, outside chronological graph failure. An old
terminal could not newly acquire that prefix under the no-late-chain lemma. -/
theorem trackedReal_new_terminal_fresh (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (covered : TerminalConsistent initial terminal state.full state.hashes)
    (message : List Payload) (fresh : state.hashes.lookup message = none)
    (first : Outcome (CompressionInput Payload Digest) Digest Digest (CompressionTable Payload Digest))
    (support : first ∈ ((iterate initial (message.map (fun block => (false, block)))).run
      RandomOracle.oracle state.full).support)
    (good : ForwardFresh initial first.state) :
    first.state.lookup (first.result, (true, terminal)) = none := by
  cases cached : first.state.lookup (first.result, (true, terminal)) with
  | none => rfl
  | some output =>
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp cached
      have member : ((first.result, (true, terminal)), output) ∈ first.state := by rw [he]; simp
      have old := iterate_data_terminal_old initial message state.full first support _ member rfl
      have chain := iterate_data_chain initial message state.full first support
      obtain ⟨later, extended⟩ := RandomOracle.run_table_extends
        (iterate initial (message.map (fun block => (false, block)))) state.full first support
      rw [extended] at chain good
      have oldChain := no_late_chain_append later state.full (first.result, (true, terminal)) output old good chain
      have registered := covered message first.result output oldChain old
      rw [fresh] at registered
      cases registered

/-- In the fresh high-level branch, the actual terminal draw and registration
have exactly the ideal hash's joint table/response law. The full data-prefix
execution has already happened and the freshness premise is proved above. -/
theorem trackedReal_new_terminal_ideal (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (covered : TerminalConsistent initial terminal state.full state.hashes)
    (message : List Payload) (fresh : state.hashes.lookup message = none)
    (first : Outcome (CompressionInput Payload Digest) Digest Digest (CompressionTable Payload Digest))
    (support : first ∈ ((iterate initial (message.map (fun block => (false, block)))).run
      RandomOracle.oracle state.full).support)
    (good : ForwardFresh initial first.state) :
    (RandomOracle.oracle first.state (first.result, (true, terminal))).map
      (fun answer => (rememberHash state.hashes message answer.2, answer.2)) =
    RandomOracle.oracle state.hashes message := by
  have terminalFresh := trackedReal_new_terminal_fresh initial terminal state covered message fresh first support good
  rw [RandomOracle.fresh first.state (first.result, (true, terminal)) terminalFresh,
    RandomOracle.fresh state.hashes message fresh, PMF.map_comp]
  simp only [Function.comp_def, rememberHash, fresh]

/-- If public search finds an unregistered message, its full terminal input
is genuinely fresh under coverage. Real sampling then registers exactly the
same exposed and hash entries as the actual ideal compression simulator. -/
theorem trackedReal_terminal_fresh_simulator (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (covered : TerminalConsistent initial terminal state.full state.hashes)
    (publicConsistent : PublicConsistent state)
    (target : Digest) (message : List Payload)
    (search : messagePrefix initial state.exposed state.exposed.length target = some message)
    (fresh : state.hashes.lookup message = none) :
    (trackedRealWorld initial terminal state (.inr (target, (true, terminal)))).map
      (fun answer => ((answer.1.exposed, answer.1.hashes), answer.2)) =
    compressionSimulator RandomOracle.oracle initial terminal
      (state.exposed, state.hashes) (target, (true, terminal)) := by
  have publicChain := (messagePrefix_sound initial state.exposed _ target message search).1
  have fullChain := publicChain.mono publicConsistent.public_subset
  have fullFresh : state.full.lookup (target, (true, terminal)) = none := by
    cases cached : state.full.lookup (target, (true, terminal)) with
    | none => rfl
    | some output =>
        obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp cached
        have member : ((target, (true, terminal)), output) ∈ state.full := by rw [he]; simp
        have registered := covered message target output fullChain member
        rw [fresh] at registered
        cases registered
  have publicFresh : state.exposed.lookup (target, (true, terminal)) = none := by
    cases cached : state.exposed.lookup (target, (true, terminal)) with
    | none => rfl
    | some output =>
        obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp cached
        have member : ((target, (true, terminal)), output) ∈ state.exposed := by rw [he]; simp
        have records := publicConsistent _ member
        simp only [fullFresh] at records
        cases records
  have realLaw :
      (trackedRealWorld initial terminal state (.inr (target, (true, terminal)))).map
        (fun answer => ((answer.1.exposed, answer.1.hashes), answer.2)) =
      (uniform Digest).map (fun output =>
        ((((target, (true, terminal)), output) :: state.exposed,
          (message, output) :: state.hashes), output)) := by
    simp [trackedRealWorld, RandomOracle.fresh state.full (target, (true, terminal)) fullFresh,
      PMF.map_comp, Function.comp_def, rememberPublic, recordLowHash, publicFresh,
      terminalMessage, search, rememberHash, fresh]
  rw [realLaw, compressionSimulator_eq]
  simp only [List.lookup_eq_findSome?, Bool.beq_eq_decide_eq, decide_eq_true_eq] at publicFresh
  simp [List.lookup_eq_findSome?, Bool.beq_eq_decide_eq, publicFresh, search,
    RandomOracle.fresh state.hashes message fresh, PMF.map_comp, Function.comp_def]

/-- Every successfully reconstructed terminal branch agrees with the actual
candidate simulator, whether its message is already registered or new. -/
theorem trackedReal_complete_terminal_simulator (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest)
    (covered : TerminalConsistent initial terminal state.full state.hashes)
    (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    (publicConsistent : PublicConsistent state)
    (target : Digest) (message : List Payload)
    (search : messagePrefix initial state.exposed state.exposed.length target = some message) :
    (trackedRealWorld initial terminal state (.inr (target, (true, terminal)))).map
      (fun answer => ((answer.1.exposed, answer.1.hashes), answer.2)) =
    compressionSimulator RandomOracle.oracle initial terminal
      (state.exposed, state.hashes) (target, (true, terminal)) := by
  cases known : state.hashes.lookup message with
  | none =>
      exact trackedReal_terminal_fresh_simulator initial terminal state covered publicConsistent
        target message search known
  | some output =>
      exact trackedReal_terminal_simulator initial terminal state completed consistent publicConsistent
        target message output search known

/-- Every terminal row absent from the public table must come from an internal
complete hash evaluation. Unlike CompletedPaths, this invariant starts from a
full-table row rather than a registered hash message. It also records the
terminal payload, ruling out private rows with other terminal-marked payloads. -/
def HiddenTerminalsComplete (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) : Prop :=
  ∀ entry ∈ state.full, entry.1.2.1 = true → entry ∉ state.exposed →
    entry.1.2.2 = terminal ∧ ∃ message, DataChain initial state.full message entry.1.1

theorem trackedReal_step_hidden_terminals (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (publicConsistent : PublicConsistent state)
    (complete : HiddenTerminalsComplete initial terminal state)
    (request : WorldInput Payload Digest) (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal state request).support) :
    HiddenTerminalsComplete initial terminal answer.1 := by
  cases request with
  | inl message =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, reachable, rfl⟩ := support
      have includes := RandomOracle.run_table_subset (prefixFreeMD initial terminal message) state.full out reachable
      obtain ⟨target, path, _, terminals⟩ := prefixFreeMD_terminal_entries initial terminal message state.full out reachable
      intro entry member marked hidden
      rcases terminals entry member marked with old | new
      · obtain ⟨payload, blocks, chain⟩ := complete entry old marked hidden
        exact ⟨payload, blocks, chain.mono includes⟩
      · subst entry
        exact ⟨rfl, message, path⟩
  | inr input =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, reachable, rfl⟩ := support
      have includes := RandomOracle.step_table_subset state.full input response reachable
      have returned : (input, response.2) ∈ rememberPublic state.exposed input response.2 := by
        cases known : state.exposed.lookup input with
        | none => simp only [rememberPublic, known]; exact List.mem_cons_self
        | some recorded =>
            obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp known
            have member : (input, recorded) ∈ state.exposed := by rw [table]; simp
            have fullKnown := publicConsistent _ member
            rw [RandomOracle.known state.full input recorded fullKnown, PMF.mem_support_pure_iff] at reachable
            subst response
            simpa only [rememberPublic, known] using member
      intro entry member marked hidden
      rcases List.mem_cons.mp (RandomOracle.step_entries state.full input response reachable member) with new | old
      · subst entry
        exact False.elim (hidden returned)
      · have oldHidden : entry ∉ state.exposed :=
          fun present => hidden (rememberPublic_includes state.exposed input response.2 present)
        obtain ⟨payload, blocks, chain⟩ := complete entry old marked oldHidden
        exact ⟨payload, blocks, chain.mono includes⟩

/-- The new full-row invariant is preserved by an arbitrary adaptive real
interaction. No collision or hidden-guess exclusion is required for it. -/
theorem trackedReal_run_hidden_terminals (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest) (publicConsistent : PublicConsistent state)
    (complete : HiddenTerminalsComplete initial terminal state)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) state).support) :
    HiddenTerminalsComplete initial terminal out.state := by
  have invariant := Program.run_preserves (trackedRealWorld initial terminal)
    (fun state => PublicConsistent state ∧ HiddenTerminalsComplete initial terminal state)
    (by intro before valid request answer reachable
        exact ⟨trackedReal_step_consistent initial terminal before valid.1 request answer reachable,
          trackedReal_step_hidden_terminals initial terminal before valid.1 valid.2 request answer reachable⟩)
    attack state ⟨publicConsistent, complete⟩ out support
  exact invariant.2

theorem trackedReal_hidden_terminals_from_empty (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support) :
    HiddenTerminalsComplete initial terminal out.state :=
  trackedReal_run_hidden_terminals initial terminal attack TrackedRealState.empty
    (by intro entry member; cases member) (by intro entry member; cases member) out support

omit [Fintype Digest] [Nonempty Digest] in
/-- If a terminal-marked input is not publicly cached and full-table search
does not recognize a message, it cannot be privately cached either. Completeness
of hidden terminals and the existing graph uniqueness justify the conclusion. -/
theorem HiddenTerminalsComplete.unrecognized_fresh {initial : Digest} {terminal : Payload}
    {state : TrackedRealState Payload Digest} (complete : HiddenTerminalsComplete initial terminal state)
    (good : ForwardFresh initial state.full) (input : CompressionInput Payload Digest)
    (marked : input.2.1 = true) (fresh : state.exposed.lookup input = none)
    (unrecognized : terminalMessage initial terminal state.full input = none) :
    state.full.lookup input = none := by
  cases cached : state.full.lookup input with
  | none => rfl
  | some output =>
      obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp cached
      have member : (input, output) ∈ state.full := by rw [table]; simp
      have hidden : (input, output) ∉ state.exposed := by
        intro present
        have missing := List.lookup_eq_none_iff.mp fresh (input, output) present
        simp at missing
      obtain ⟨payload, blocks, path⟩ := complete (input, output) member marked hidden
      change input.2.2 = terminal at payload
      obtain ⟨injective, avoid⟩ := freshOutputs_graph good.outputs
      have found := messagePrefix_complete injective avoid path
      have recognized : terminalMessage initial terminal state.full input = some blocks := by
        simp only [terminalMessage, marked, payload, and_self, ↓reduceIte]
        exact found
      rw [recognized] at unrecognized
      cases unrecognized

/-- Reconstruct the public compression cache from the outer transcript.
High hash queries make no public-cache entry. This fold is a mathematical
observation and is not charged as an executed adversary or simulator program. -/
def publicHistory (before : CompressionTable Payload Digest)
    (trace : List (WorldInput Payload Digest × Digest)) : CompressionTable Payload Digest :=
  trace.foldl (fun seen entry => match entry.1 with
    | .inl _ => seen
    | .inr input => rememberPublic seen input entry.2) before

/-- The tracked public table is exactly determined by the complete outer
transcript, for arbitrary adaptive queries and local coins. -/
theorem trackedReal_public_history (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : TrackedRealState Payload Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (support : out ∈ (attack.run (trackedRealWorld initial terminal) state).support) :
    out.state.exposed = publicHistory state.exposed out.trace := by
  apply Program.run_observe_trace (trackedRealWorld initial terminal) TrackedRealState.exposed
    (fun seen request output => match request with
      | .inl _ => seen
      | .inr input => rememberPublic seen input output) _ attack state out support
  intro before request answer reachable
  cases request <;>
    rw [trackedRealWorld, PMF.mem_support_map_iff] at reachable <;>
    obtain ⟨response, _, rfl⟩ := reachable <;> rfl

/-- A real transition cannot set the hidden-parent guess flag when it was
false and the current public compression parent is not a hidden data output.
No graph condition is needed for this forward flag-preservation statement. -/
theorem trackedReal_step_visible (initial : Digest) (terminal : Payload)
    (state : TrackedRealState Payload Digest) (notGuessed : state.guessed = false)
    (request : WorldInput Payload Digest)
    (visible : ∀ input, request = .inr input → input.1 ∉ hiddenDataOutputs state)
    (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal state request).support) :
    answer.1.guessed = false := by
  cases request with
  | inl message =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, _, rfl⟩ := support
      exact notGuessed
  | inr input =>
      rw [trackedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, _, rfl⟩ := support
      simp only [markHiddenGuess, notGuessed, visible input rfl, decide_false, Bool.or_false,
        ite_self]

end Foundation.Hash
