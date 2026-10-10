import Foundation.Constructions.Hash.CoordinateRealWorld
import Foundation.Crypto.Semantics.Oracle.RandomOracleValues

/-! Concrete state-correspondence obligations for the two coordinate worlds.
Revealed coordinates really agree with the fixed function on all reachable eager
executions. Deterministic decoding and data-table lemmas isolate where collision
and hidden-guess exclusions enter. Preservation of a full real/ideal relation
and the final probability coupling are still separate proof obligations. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

local instance relationCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance relationGraphBEq : BEq ((Digest ⊕ Label) × Payload) := instBEqOfDecidableEq
local instance relationLabelBEq : BEq Label := instBEqOfDecidableEq

/-- A fixed coordinate function's actual transition is supported by the
lazy-coordinate transition with the same independent hash kernel. Every
component of the actual state and response is retained; no probability masses
are equated. -/
theorem latent_coordinate_eager_step_support (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentWorldState Payload Digest Label)
    (request : WorldInput Payload Digest) (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle state request).support) :
    answer ∈ (latentWorld initial terminal hashOracle state request).support := by
  unfold latentCoordinateWorld Program.statefulOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, same⟩ := support
  have lazySupport := Program.run_support_state_map id
    (Program.adaptOracle latentContextRequest id
      (RandomOracle.withContext (simulatorBackend hashOracle) (RandomOracle.eager function)))
    (Program.adaptOracle latentContextRequest id
      (RandomOracle.withContext (simulatorBackend hashOracle) RandomOracle.oracle))
    (by intro backend query response present
        have present' : response ∈ (RandomOracle.withContext (simulatorBackend hashOracle)
            (RandomOracle.eager function) backend (latentContextRequest query)).support := by
          change response ∈ (PMF.map id _).support at present
          rwa [PMF.map_id] at present
        have transferred := RandomOracle.eager_context_step_support function (simulatorBackend hashOracle)
          backend (latentContextRequest query) response present'
        change (response.1, response.2) ∈ (PMF.map id _).support
        rw [PMF.map_id]
        exact transferred)
    (latentProgram initial terminal state.1 request) state.2 out reachable
  have supported : answer ∈ (latentWorld initial terminal hashOracle state request).support := by
    unfold latentWorld Program.statefulOracle
    rw [PMF.mem_support_map_iff]
    refine ⟨out, ?_, same⟩
    rw [← latent_backend_context hashOracle]
    simpa only [Program.mapState, id_eq] using lazySupport
  exact supported

/-- A fixed coordinate function's actual transition is supported by the
lazy-coordinate transition with the same independent hash kernel. Thus the
existing controller/cache coherence invariant applies to each fixed function. -/
theorem latent_coordinate_eager_step_coherent (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentWorldState Payload Digest Label) (valid : LatentCoherent state)
    (request : WorldInput Payload Digest) (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle state request).support) :
    LatentCoherent answer.1 := by
  exact latent_step_coherent initial terminal state valid request answer
    (latent_coordinate_eager_step_support initial terminal function hashOracle state request answer support)

/-- Fixed-coordinate support transport applies to the entire adaptive outer
execution and retains its full public transcript. It is support inclusion. -/
theorem latent_coordinate_eager_run_support {Result : Type} (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (attack : Program (WorldInput Payload Digest) Digest Result) (state : LatentWorldState Payload Digest Label)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      hashOracle) state).support) :
    out ∈ (attack.run (latentWorld initial terminal hashOracle) state).support := by
  have transferred := Program.run_support_state_map id _ _
    (by intro before request answer reachable
        simpa only [id_eq, Prod.mk.eta] using
          latent_coordinate_eager_step_support initial terminal function hashOracle before request answer reachable)
    attack state out support
  simpa only [Program.mapState, id_eq] using transferred

/-- Fixed-coordinate agreement is preserved by the actual outer transition.
The initial agreement with the coordinate cache is explicit. -/
theorem latent_coordinate_eager_step_values (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentWorldState Payload Digest Label) (valid : LatentCoherent state)
    (values : RandomOracle.TableValues function state.1.revealed)
    (request : WorldInput Payload Digest) (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle state request).support) :
    RandomOracle.TableValues function answer.1.1.revealed := by
  have coherent := latent_coordinate_eager_step_coherent initial terminal function hashOracle state valid request answer support
  unfold latentCoordinateWorld Program.statefulOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, same⟩ := support
  have stored : RandomOracle.TableValues function state.2.2 := by rwa [← valid.1]
  have preserved := Program.run_preserves
    (Program.adaptOracle latentContextRequest id
      (RandomOracle.withContext (simulatorBackend hashOracle) (RandomOracle.eager function)))
    (fun backend => RandomOracle.TableValues function backend.2)
    (by intro backend values query response present
        apply RandomOracle.eager_context_step_values function (simulatorBackend hashOracle) backend values
          (latentContextRequest query) response
        change response ∈ (PMF.map id _).support at present
        rwa [PMF.map_id] at present)
    (latentProgram initial terminal state.1 request) state.2 stored out reachable
  have backendSame : out.state = answer.1.2 := congrArg (fun result => result.1.2) same
  rw [backendSame, ← coherent.1] at preserved
  exact preserved

/-- Every fixed eager coordinate function preserves coherence through the
entire interaction, with any independent hash kernel. No finite label type or
mixture of functions is needed for this support invariant. -/
theorem latent_eager_coherent {Result : Type} (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (supply : List Label) (attack : Program (WorldInput Payload Digest) Digest Result)
    (function : Label → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
      (LatentState.empty supply, ([], []))).support) : LatentCoherent out.state :=
  Program.run_preserves _ LatentCoherent (latent_coordinate_eager_step_coherent initial terminal function hashOracle)
    attack _ (latent_empty_coherent supply) out support

/-- Revealed entries agree with the fixed function after every actual adaptive
execution. This also holds for a fixed finite hash function's total extension. -/
theorem latent_eager_revealed_values {Result : Type} (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (supply : List Label) (attack : Program (WorldInput Payload Digest) Digest Result)
    (function : Label → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
      (LatentState.empty supply, ([], []))).support) : RandomOracle.TableValues function out.state.1.revealed := by
  have invariant := Program.run_preserves
    (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
    (fun state => LatentCoherent state ∧ RandomOracle.TableValues function state.1.revealed)
    (by intro state valid request answer reachable
        exact ⟨latent_coordinate_eager_step_coherent initial terminal function hashOracle state valid.1 request answer reachable,
          latent_coordinate_eager_step_values initial terminal function hashOracle state valid.1 valid.2 request answer reachable⟩)
    attack (LatentState.empty supply, ([], []))
    (by exact ⟨latent_empty_coherent supply, fun _ member => by cases member⟩) out support
  exact invariant.2

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
/-- A row in the inverse public lookup still denotes its real fixed coordinate. -/
theorem revealed_inverse_entry (function : Label → Digest) (state : LatentState Payload Digest Label)
    (values : RandomOracle.TableValues function state.revealed) (value : Digest) (label : Label)
    (member : (value, label) ∈ state.revealed.map (fun entry => (entry.2, entry.1))) : value = function label := by
  obtain ⟨entry, stored, same⟩ := List.mem_map.mp member
  calc
    value = entry.2 := (congrArg Prod.fst same).symm
    _ = function entry.1 := values entry stored
    _ = function label := congrArg function (congrArg Prod.snd same)

omit [DecidableEq Payload] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem revealed_inverse_consistent (function : Label → Digest) (injective : Function.Injective function)
    (state : LatentState Payload Digest Label) (values : RandomOracle.TableValues function state.revealed) :
    RandomOracle.TableConsistent (state.revealed.map (fun entry => (entry.2, entry.1))) := by
  apply RandomOracle.TableConsistent.of_functional
  intro value left right hl hr
  exact injective ((revealed_inverse_entry function state values value left hl).symm.trans
    (revealed_inverse_entry function state values value right hr))

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
theorem revealed_inverse_lookup (function : Label → Digest) (injective : Function.Injective function)
    (state : LatentState Payload Digest Label) (values : RandomOracle.TableValues function state.revealed)
    (label : Label) (output : Digest) (known : state.revealed.lookup label = some output) :
    (state.revealed.map (fun entry => (entry.2, entry.1))).lookup output = some label := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp known
  apply revealed_inverse_consistent function injective state values (output, label)
  apply List.mem_map.mpr
  exact ⟨(label, output), by rw [same]; simp, rfl⟩

omit [DecidableEq Payload] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
/-- Decoding the controller's actual parent choice always gives the supplied
digest, even without injectivity. Equality of symbolic parents is stronger. -/
theorem latentParent_value (initial : Digest) (function : Label → Digest)
    (state : LatentState Payload Digest Label) (values : RandomOracle.TableValues function state.revealed)
    (value : Digest) : latentValue function (latentParent initial state value) = value := by
  by_cases iv : value = initial
  · simp [latentParent, iv, latentValue]
  · simp only [latentParent, iv, ↓reduceIte]
    cases known : (state.revealed.map (fun entry => (entry.2, entry.1))).lookup value with
    | none => rfl
    | some label =>
        obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp known
        have member : (value, label) ∈ state.revealed.map (fun entry => (entry.2, entry.1)) := by rw [same]; simp
        exact (revealed_inverse_entry function state values value label member).symm

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
/-- Outside coordinate collisions and a return to the IV, a published vertex
is recovered with its original number by the executable inverse lookup. -/
theorem latentParent_revealed (initial : Digest) (function : Label → Digest)
    (injective : Function.Injective function) (state : LatentState Payload Digest Label)
    (values : RandomOracle.TableValues function state.revealed) (label : Label)
    (avoid : function label ≠ initial) (known : state.revealed.lookup label = some (function label)) :
    latentParent initial state (function label) = .inr label := by
  simp only [latentParent, avoid, ↓reduceIte,
    revealed_inverse_lookup function injective state values label (function label) known]

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
/-- An unexposed vertex is not recovered by the inverse table. A public query
using this digest is therefore precisely the hidden-parent guessing case. -/
theorem latentParent_hidden (initial : Digest) (function : Label → Digest)
    (injective : Function.Injective function) (state : LatentState Payload Digest Label)
    (values : RandomOracle.TableValues function state.revealed) (label : Label)
    (avoid : function label ≠ initial) (hidden : state.revealed.lookup label = none) :
    latentParent initial state (function label) = .inl (function label) := by
  have missing : (state.revealed.map (fun entry => (entry.2, entry.1))).lookup (function label) = none := by
    cases known : (state.revealed.map (fun entry => (entry.2, entry.1))).lookup (function label) with
    | none => rfl
    | some other =>
        obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp known
        have member : (function label, other) ∈ state.revealed.map (fun entry => (entry.2, entry.1)) := by rw [same]; simp
        have equal := injective (revealed_inverse_entry function state values (function label) other member)
        subst other
        have stored : (label, function label) ∈ state.revealed := by
          obtain ⟨entry, stored, pair⟩ := List.mem_map.mp member
          have sameEntry : entry = (label, function label) :=
            Prod.ext (congrArg Prod.snd pair) (congrArg Prod.fst pair)
          rwa [sameEntry] at stored
        have impossible := List.lookup_eq_none_iff.mp hidden (label, function label) stored
        simp at impossible
  simp [latentParent, avoid, missing]


/-- Membership correspondence of all data edges, independent of list order.
A revealed graph child has its decoded edge in the public compression table.
Preservation of this relation by the two worlds remains to be proved. -/
structure LatentDataRelation (function : Label → Digest) (full : CompressionTable Payload Digest)
    (state : LatentState Payload Digest Label) : Prop where
  sound : latentDecodedGraph function state ⊆ full
  complete : ∀ entry ∈ full, entry.1.2.1 = false → entry ∈ latentDecodedGraph function state
  published : ∀ edge ∈ state.graph, state.revealed.lookup edge.2 ≠ none →
    latentDecodedEdge function edge ∈ state.exposed

omit [Fintype Digest] [Nonempty Digest] in
/-- A stored symbolic child denotes exactly the real compression-cache value. -/
theorem LatentDataRelation.known {function : Label → Digest} {full : CompressionTable Payload Digest}
    {state : LatentState Payload Digest Label} (relation : LatentDataRelation function full state)
    (consistent : RandomOracle.TableConsistent full) (parent : Digest ⊕ Label) (block : Payload)
    (child : Label) (known : state.graph.lookup (parent, block) = some child) :
    full.lookup (latentValue function parent, (false, block)) = some (function child) := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp known
  have stored : latentDecodedEdge function ((parent, block), child) ∈ full := by
    apply relation.sound
    apply List.mem_map.mpr
    exact ⟨((parent, block), child), by rw [same]; simp, rfl⟩
  have result := consistent _ stored
  simpa only [latentDecodedEdge, List.lookup_eq_findSome?, beq_iff_eq] using result


omit [Fintype Digest] [Nonempty Digest] in
/-- If decoding cannot alias a graph parent to the chosen symbolic parent,
absence of a symbolic data key implies absence of the actual compression key. -/
theorem LatentDataRelation.fresh {function : Label → Digest} {full : CompressionTable Payload Digest}
    {state : LatentState Payload Digest Label} (relation : LatentDataRelation function full state)
    (parent : Digest ⊕ Label) (block : Payload)
    (canonical : ∀ edge ∈ state.graph,
      latentValue function edge.1.1 = latentValue function parent → edge.1.1 = parent)
    (missing : state.graph.lookup (parent, block) = none) :
    full.lookup (latentValue function parent, (false, block)) = none := by
  cases known : full.lookup (latentValue function parent, (false, block)) with
  | none => rfl
  | some output =>
      obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp known
      have stored : ((latentValue function parent, (false, block)), output) ∈ full := by rw [same]; simp
      have decoded := relation.complete _ stored rfl
      obtain ⟨edge, member, edgeEq⟩ := List.mem_map.mp decoded
      have parents : latentValue function edge.1.1 = latentValue function parent :=
        congrArg (fun entry => entry.1.1) edgeEq
      have blocks : edge.1.2 = block := congrArg (fun entry => entry.1.2.2) edgeEq
      have key : edge.1 = (parent, block) := Prod.ext (canonical edge member parents) blocks
      have impossible := List.lookup_eq_none_iff.mp missing edge member
      simp [key] at impossible

omit [Fintype Digest] [Nonempty Digest] in
/-- A child of a still-unexposed data input cannot already be revealed, since
publication of that child would have exposed this very compression input. -/
theorem LatentDataRelation.pending {function : Label → Digest} {full : CompressionTable Payload Digest}
    {state : LatentState Payload Digest Label} (relation : LatentDataRelation function full state)
    (parent : Digest ⊕ Label) (block : Payload) (child : Label)
    (known : state.graph.lookup (parent, block) = some child)
    (freshPublic : state.exposed.lookup (latentValue function parent, (false, block)) = none) :
    state.revealed.lookup child = none := by
  by_contra disclosed
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp known
  have member : ((parent, block), child) ∈ state.graph := by rw [same]; simp
  have exposed := relation.published _ member disclosed
  have impossible := List.lookup_eq_none_iff.mp freshPublic _ exposed
  simp [latentDecodedEdge] at impossible

omit [Fintype Digest] [Nonempty Digest] in
/-- Thus the executable low-level choice reuses the pending graph number,
without allocating a second value for the already existing real data edge. -/
theorem LatentDataRelation.choose_known {function : Label → Digest} {full : CompressionTable Payload Digest}
    {state : LatentState Payload Digest Label} (relation : LatentDataRelation function full state)
    (initial : Digest) (values : RandomOracle.TableValues function state.revealed)
    (value : Digest) (block : Payload) (child : Label)
    (known : state.graph.lookup (latentParent initial state value, block) = some child)
    (freshPublic : state.exposed.lookup (value, (false, block)) = none) :
    chooseLatent initial state (value, (false, block)) = (state, some child) := by
  have pending := relation.pending (latentParent initial state value) block child known
    (by simpa only [latentParent_value initial function state values value] using freshPublic)
  simp only [chooseLatent, ↓reduceIte, known, pending]

omit [Fintype Digest] [Nonempty Digest] in
/-- Every genuinely hidden real data output is the value of an unrevealed
symbolic coordinate, provided this concrete data/publication relation holds.
This is an event implication, not a probability transfer theorem. -/
theorem LatentDataRelation.hidden_coordinate {function : Label → Digest}
    {real : TrackedRealState Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function real.full state) (publicSame : real.exposed = state.exposed)
    (value : Digest) (hidden : value ∈ hiddenDataOutputs real) :
    ∃ label, state.revealed.lookup label = none ∧ function label = value := by
  obtain ⟨entry, stored, selected⟩ := List.mem_filterMap.mp hidden
  by_cases condition : entry.1.2.1 = false ∧ entry ∉ real.exposed
  · simp [condition.1, condition.2] at selected
    obtain ⟨edge, member, decoded⟩ := List.mem_map.mp (relation.complete entry stored condition.1)
    refine ⟨edge.2, ?_, ?_⟩
    · by_contra disclosed
      have exposed := relation.published edge member disclosed
      rw [decoded, ← publicSame] at exposed
      exact condition.2 exposed
    · exact (congrArg Prod.snd decoded).trans selected
  · simp [condition] at selected

omit [Fintype Digest] [Nonempty Digest] in
/-- Under the state relation, the real hidden-parent guessing test implies the
actual ideal monitor test. The relation's preservation is still required before
using the already proved ideal online probability bound for the real world. -/
theorem LatentDataRelation.hidden_guess [Fintype Label] {function : Label → Digest}
    {real : TrackedRealState Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function real.full state) (publicSame : real.exposed = state.exposed)
    (backend : RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)
    (input : CompressionInput Payload Digest) (hidden : input.1 ∈ hiddenDataOutputs real) :
    latentGuessHit function (state, backend) (.inr input) = true := by
  classical
  obtain ⟨label, pending, same⟩ := relation.hidden_coordinate publicSame input.1 hidden
  simp only [latentGuessHit, decide_eq_true_eq]
  refine ⟨label, ?_, ?_⟩
  · apply List.mem_filter.mpr
    exact ⟨Finset.mem_toList.mpr (Finset.mem_univ label), by simp only [pending, decide_true]⟩
  · simp [nextLowGuesses, same]

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
/-- Outside a hidden-coordinate guess, every graph parent decoding to the
public input is exactly the parent selected by the executable inverse lookup.
Literal stability is explicit: its preservation is a further bad-event duty. -/
theorem latentParent_canonical (initial : Digest) (function : Label → Digest)
    (injective : Function.Injective function) (state : LatentState Payload Digest Label)
    (values : RandomOracle.TableValues function state.revealed)
    (avoid : ∀ label, function label ≠ initial) (value : Digest)
    (noGuess : ∀ label, state.revealed.lookup label = none → function label ≠ value)
    (literalStable : ∀ edge ∈ state.graph, ∀ literal, edge.1.1 = .inl literal →
      latentParent initial state literal = .inl literal) :
    ∀ edge ∈ state.graph, latentValue function edge.1.1 = value →
      edge.1.1 = latentParent initial state value := by
  intro edge member decoded
  cases parent : edge.1.1 with
  | inl literal =>
      have same : literal = value := by simpa [parent, latentValue] using decoded
      rw [← same]
      exact (literalStable edge member literal parent).symm
  | inr label =>
      have same : function label = value := by simpa [parent, latentValue] using decoded
      cases known : state.revealed.lookup label with
      | none => exact False.elim (noGuess label known same)
      | some output =>
          have outputEq := RandomOracle.TableValues.lookup values known
          have published : state.revealed.lookup label = some (function label) := by
            simpa only [outputEq] using known
          rw [← same]
          exact (latentParent_revealed initial function injective state values label
            (avoid label) published).symm

omit [Fintype Digest] [Nonempty Digest] in
/-- Concrete data-cache correspondence for a public input. The right side is
the actual symbolic lookup, with its answer decoded, not a second real cache.
The hypotheses exclude aliases and hidden guesses; preservation and probability
bounds for these hypotheses are not asserted by this deterministic lemma. -/
theorem LatentDataRelation.data_lookup {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state)
    (consistent : RandomOracle.TableConsistent full) (initial : Digest)
    (injective : Function.Injective function)
    (values : RandomOracle.TableValues function state.revealed)
    (avoid : ∀ label, function label ≠ initial) (value : Digest) (block : Payload)
    (noGuess : ∀ label, state.revealed.lookup label = none → function label ≠ value)
    (literalStable : ∀ edge ∈ state.graph, ∀ literal, edge.1.1 = .inl literal →
      latentParent initial state literal = .inl literal) :
    full.lookup (value, (false, block)) =
      (state.graph.lookup (latentParent initial state value, block)).map function := by
  have canonical := latentParent_canonical initial function injective state values avoid value noGuess literalStable
  cases known : state.graph.lookup (latentParent initial state value, block) with
  | none =>
      have fresh := relation.fresh (latentParent initial state value) block
        (by intro edge member equal
            apply canonical edge member
            simpa only [latentParent_value initial function state values value] using equal) known
      simpa only [latentParent_value initial function state values value, Option.map_none] using fresh
  | some child =>
      have cached := relation.known consistent (latentParent initial state value) block child known
      simpa only [latentParent_value initial function state values value, Option.map_some] using cached

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Reserving one genuinely unpublished child preserves both directions of
data-edge membership and the publication obligation. Supply changes alone do
not alter these obligations. No freshness of decoded compression keys is hidden
in this lemma; that separate condition is needed for cache consistency. -/
theorem LatentDataRelation.reserve_edge {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state) (parent : Digest ⊕ Label)
    (block : Payload) (child : Label) (rest : List Label)
    (pending : state.revealed.lookup child = none) :
    LatentDataRelation function
      (latentDecodedEdge function ((parent, block), child) :: full)
      { state with graph := ((parent, block), child) :: state.graph, supply := rest } := by
  refine ⟨?_, ?_, ?_⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | old
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (relation.sound old)
  · intro entry member data
    rcases List.mem_cons.mp member with rfl | old
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (relation.complete entry old data)
  · intro edge member disclosed
    rcases List.mem_cons.mp member with rfl | old
    · exact False.elim (disclosed pending)
    · exact relation.published edge old disclosed

omit [Fintype Digest] [Nonempty Digest] in
/-- A real internal data step can follow the executable symbolic reservation.
For a fresh symbolic edge it inserts the selected fixed coordinate into the
real table; for a known edge it leaves the real table unchanged. Key alias
exclusion and available fresh supply are explicit. This is a deterministic
state step, not yet the probabilistic coupling of the complete worlds. -/
theorem latentAdvance_data_relation (initial : Digest) (function : Label → Digest)
    (state : LatentState Payload Digest Label) (full : CompressionTable Payload Digest)
    (relation : LatentDataRelation function full state)
    (consistent : RandomOracle.TableConsistent full)
    (freshSupply : state.FreshSupply) (available : state.supply ≠ [])
    (parent : Digest ⊕ Label) (block : Payload)
    (canonical : ∀ edge ∈ state.graph,
      latentValue function edge.1.1 = latentValue function parent → edge.1.1 = parent) :
    ∃ nextFull,
      LatentDataRelation function nextFull (latentAdvance initial state parent block).1 ∧
      RandomOracle.TableConsistent nextFull ∧
      nextFull.lookup (latentValue function parent, (false, block)) =
        some (latentValue function (latentAdvance initial state parent block).2) := by
  cases known : state.graph.lookup (parent, block) with
  | some child =>
      refine ⟨full, ?_, consistent, ?_⟩
      · simpa only [latentAdvance, known] using relation
      · simpa only [latentAdvance, known, latentValue, Sum.elim_inr] using
          relation.known consistent parent block child known
  | none =>
      have missing := relation.fresh parent block canonical known
      cases supply : state.supply with
      | nil => exact False.elim (available supply)
      | cons child rest =>
          have pending := freshSupply child (by rw [supply]; exact List.mem_cons_self)
          let edge := latentDecodedEdge function ((parent, block), child)
          refine ⟨edge :: full, ?_, ?_, ?_⟩
          · simpa only [latentAdvance, known, reserveLabel, supply] using
              relation.reserve_edge parent block child rest pending
          · have fresh : full.lookup edge.1 = none := by
              simpa only [edge, latentDecodedEdge] using missing
            have proof := RandomOracle.TableConsistent.cons consistent edge.1 edge.2 fresh
            simpa only [List.lookup_eq_findSome?, beq_iff_eq] using proof
          · simp [edge, latentDecodedEdge, latentAdvance, known, reserveLabel, supply, latentValue]

/-- Every fresh compression key not recognized as a complete message uses
the next available coordinate through the existing local-draw interpreter.
This includes both data inputs and unrecognized terminal-marked inputs. -/
theorem coordinate_real_local_fresh (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (full : CompressionTable Payload Digest)
    (hashes : RandomOracle.Table (List Payload) Digest) (coordinates : RandomOracle.Table Label Digest)
    (child : Label) (rest : List Label) (flag : Bool) (input : CompressionInput Payload Digest)
    (fresh : full.lookup input = none)
    (unrecognized : terminalMessage initial terminal full input = none)
    (coordinateFresh : coordinates.lookup child = none)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld (RandomOracle.eager function) hashOracle)
      (full, ((child :: rest, flag), (hashes, coordinates))) input =
      PMF.pure (((input, function child) :: full,
        ((rest, flag), (hashes, (child, function child) :: coordinates))), function child) := by
  simp only [List.lookup_eq_findSome?, beq_iff_eq] at fresh coordinateFresh
  simp [Program.statefulOracle, simulatorProgram, List.lookup_eq_findSome?, beq_iff_eq,
    fresh, unrecognized, Program.run, realCoordinateWorld_eq (hashOracle := hashOracle), RandomOracle.eager,
    coordinateFresh, PMF.pure_map]

/-- The actual real-world compression interpreter, on a fresh data key and
fresh available coordinate, inserts exactly that coordinate value. Hash state
and overflow flag are unchanged; the coordinate cache records the draw. -/
theorem coordinate_real_data_fresh (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (full : CompressionTable Payload Digest)
    (hashes : RandomOracle.Table (List Payload) Digest) (coordinates : RandomOracle.Table Label Digest)
    (child : Label) (rest : List Label) (flag : Bool) (value : Digest) (block : Payload)
    (fresh : full.lookup (value, (false, block)) = none)
    (coordinateFresh : coordinates.lookup child = none)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld (RandomOracle.eager function) hashOracle)
      (full, ((child :: rest, flag), (hashes, coordinates))) (value, (false, block)) =
      PMF.pure ((((value, (false, block)), function child) :: full,
        ((rest, flag), (hashes, (child, function child) :: coordinates))), function child) := by
  exact coordinate_real_local_fresh initial terminal function full hashes coordinates child rest flag
    (value, (false, block)) fresh (by simp [terminalMessage]) coordinateFresh hashOracle

/-- Cached compression inputs do not consume a coordinate or change state. -/
theorem coordinate_real_known (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (full : CompressionTable Payload Digest)
    (backend : RealCoordinateState Payload Digest Label) (input : CompressionInput Payload Digest)
    (output : Digest) (known : full.lookup input = some output)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld (RandomOracle.eager function) hashOracle) (full, backend) input =
      PMF.pure ((full, backend), output) := by
  simp only [List.lookup_eq_findSome?, beq_iff_eq] at known
  simp [Program.statefulOracle, simulatorProgram, List.lookup_eq_findSome?, beq_iff_eq,
    known, Program.run, PMF.pure_map]

/-- Actual supported internal-data transitions preserve the concrete table
relation, cache consistency, decoded answer, and remaining-supply agreement.
Only the hash data step is covered here; terminal and public publication steps
remain necessary for the complete real/ideal coupling. -/
theorem latentAdvance_real_step (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (function : Label → Digest) (state : LatentState Payload Digest Label)
    (full : CompressionTable Payload Digest)
    (hashes : RandomOracle.Table (List Payload) Digest) (coordinates : RandomOracle.Table Label Digest)
    (flag : Bool) (relation : LatentDataRelation function full state)
    (consistent : RandomOracle.TableConsistent full) (freshSupply : state.FreshSupply)
    (privateFresh : ∀ label ∈ state.supply, coordinates.lookup label = none)
    (available : state.supply ≠ []) (parent : Digest ⊕ Label) (block : Payload)
    (canonical : ∀ edge ∈ state.graph,
      latentValue function edge.1.1 = latentValue function parent → edge.1.1 = parent)
    (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld (RandomOracle.eager function) hashOracle)
      (full, ((state.supply, flag), (hashes, coordinates)))
      (latentValue function parent, (false, block))).support) :
    LatentDataRelation function answer.1.1 (latentAdvance initial state parent block).1 ∧
    RandomOracle.TableConsistent answer.1.1 ∧
    answer.2 = latentValue function (latentAdvance initial state parent block).2 ∧
    answer.1.2.1.1 = (latentAdvance initial state parent block).1.supply := by
  cases known : state.graph.lookup (parent, block) with
  | some child =>
      have execution := coordinate_real_known initial terminal function full
        ((state.supply, flag), (hashes, coordinates)) _ _
        (relation.known consistent parent block child known) hashOracle
      rw [execution, PMF.mem_support_pure_iff] at support
      subst answer
      simpa only [latentAdvance, known, latentValue, Sum.elim_inr] using
        (show LatentDataRelation function full state ∧ RandomOracle.TableConsistent full ∧
          function child = function child ∧ state.supply = state.supply from
          ⟨relation, consistent, rfl, rfl⟩)
  | none =>
      have missing := relation.fresh parent block canonical known
      cases supply : state.supply with
      | nil => exact False.elim (available supply)
      | cons child rest =>
          have member : child ∈ state.supply := by rw [supply]; exact List.mem_cons_self
          have execution := coordinate_real_data_fresh initial terminal function full hashes coordinates
            child rest flag (latentValue function parent) block missing (privateFresh child member) hashOracle
          rw [supply, execution, PMF.mem_support_pure_iff] at support
          subst answer
          simp only [latentAdvance, known, reserveLabel, supply, latentValue, Sum.elim_inr]
          refine ⟨relation.reserve_edge parent block child rest (freshSupply child member), ?_, True.intro, True.intro⟩
          have normalized : full.lookup (latentValue function parent, (false, block)) = none := missing
          have coherent := RandomOracle.TableConsistent.cons consistent _ (function child) normalized
          simpa only [latentValue, List.lookup_eq_findSome?, beq_iff_eq] using coherent

end Foundation.Hash

