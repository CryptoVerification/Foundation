import Foundation.Constructions.Hash.LatentRelation

/-! Publication of numbered vertices in the existing ideal controller.
A graph child has only one incoming data edge. This structural invariant is
separate from collisions of the digest values obtained by decoding labels. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

local instance publicationGraphBEq : BEq ((Digest ⊕ Label) × Payload) := instBEqOfDecidableEq
local instance publicationLabelBEq : BEq Label := instBEqOfDecidableEq
local instance publicationCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq

/-- A reserved child identifies its incoming symbolic data key. This is not
injectivity of the digest-valued coordinate function. -/
def LatentState.ChildrenUnique (state : LatentState Payload Digest Label) : Prop :=
  ∀ left ∈ state.graph, ∀ right ∈ state.graph, left.2 = right.2 → left.1 = right.1

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem LatentState.ChildrenUnique.cons {state : LatentState Payload Digest Label}
    (unique : state.ChildrenUnique) (key : (Digest ⊕ Label) × Payload) (child : Label)
    (fresh : ∀ edge ∈ state.graph, edge.2 ≠ child) (rest : List Label) :
    ({ state with graph := (key, child) :: state.graph, supply := rest }).ChildrenUnique := by
  intro left hl right hr equal
  rcases List.mem_cons.mp hl with rfl | hl
  · rcases List.mem_cons.mp hr with rfl | hr
    · rfl
    · exact False.elim (fresh right hr equal.symm)
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact False.elim (fresh left hl equal)
    · exact unique left hl right hr equal

omit [Fintype Digest] [Nonempty Digest] in
theorem latentAdvance_children_unique (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : state.AllocationValid) (unique : state.ChildrenUnique)
    (parent : Digest ⊕ Label) (block : Payload) :
    (latentAdvance initial state parent block).1.ChildrenUnique := by
  cases known : state.graph.lookup (parent, block) with
  | some child => simpa only [latentAdvance, known] using unique
  | none =>
      cases supply : state.supply with
      | nil => simpa only [latentAdvance, known, reserveLabel, supply, LatentState.ChildrenUnique] using unique
      | cons child rest =>
          have fresh : ∀ edge ∈ state.graph, edge.2 ≠ child := by
            intro edge member equal
            apply valid.2 edge member
            rw [equal, supply]
            exact List.mem_cons_self
          simpa only [latentAdvance, known, reserveLabel, supply] using
            unique.cons (parent, block) child fresh rest

omit [Fintype Digest] [Nonempty Digest] in
theorem reserveMessage_children_unique (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : state.AllocationValid) (unique : state.ChildrenUnique)
    (parent : Digest ⊕ Label) (message : List Payload) :
    (reserveMessage initial state parent message).ChildrenUnique := by
  induction message generalizing state parent with
  | nil => exact unique
  | cons block rest ih =>
      exact ih _ (latentAdvance_allocation initial state valid parent block).valid
        (latentAdvance_children_unique initial state valid unique parent block) _

omit [Fintype Digest] [Nonempty Digest] in
theorem chooseLatent_children_unique (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : state.AllocationValid) (unique : state.ChildrenUnique)
    (input : CompressionInput Payload Digest) : (chooseLatent initial state input).1.ChildrenUnique := by
  unfold chooseLatent
  split
  · dsimp only
    split
    · split
      · exact unique
      · cases supply : state.supply <;> simpa only [reserveLabel, supply, LatentState.ChildrenUnique] using unique
    · cases supply : state.supply with
      | nil => simpa only [reserveLabel, supply, LatentState.ChildrenUnique] using unique
      | cons child rest =>
          have fresh : ∀ edge ∈ state.graph, edge.2 ≠ child := by
            intro edge member equal
            apply valid.2 edge member
            rw [equal, supply]
            exact List.mem_cons_self
          simpa only [reserveLabel, supply] using
            unique.cons (latentParent initial state input.1, input.2.2) child fresh rest
  · cases supply : state.supply <;> simpa only [reserveLabel, supply, LatentState.ChildrenUnique] using unique

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem finishLatent_children_unique (state : LatentState Payload Digest Label)
    (unique : state.ChildrenUnique) (input : CompressionInput Payload Digest)
    (selected : Option Label) (output : Digest) :
    (finishLatent state input selected output).ChildrenUnique := by
  cases selected <;> exact unique

/-- The unique-incoming-edge invariant holds for actual adaptive lazy-world
transitions, including exhaustion and arbitrary sampled digest collisions. -/
theorem latent_step_children_unique (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (state : LatentWorldState Payload Digest Label) (valid : state.1.AllocationValid)
    (unique : state.1.ChildrenUnique) (request : WorldInput Payload Digest)
    (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentWorld initial terminal hashOracle state request).support) : answer.1.1.ChildrenUnique := by
  rcases state with ⟨control, hashes, coordinates⟩
  rw [latentWorld_eq (hashOracle := hashOracle)] at support
  cases request with
  | inl message =>
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨result, _, rfl⟩ := support
      exact reserveMessage_children_unique initial control valid unique (.inl initial) message
  | inr input =>
      cases cached : control.exposed.lookup input with
      | some output =>
          simp only [cached, PMF.mem_support_pure_iff] at support
          subst answer
          exact unique
      | none =>
          simp only [cached] at support
          cases recognized : terminalMessage initial terminal control.exposed input with
          | some message =>
              simp only [recognized] at support
              rw [PMF.mem_support_map_iff] at support
              obtain ⟨result, _, rfl⟩ := support
              exact unique
          | none =>
              simp only [recognized] at support
              cases selected : (chooseLatent initial control input).2 with
              | none =>
                  simp only [selected] at support
                  rw [PMF.mem_support_map_iff] at support
                  obtain ⟨output, _, rfl⟩ := support
                  simpa only [selected] using finishLatent_children_unique _
                    (chooseLatent_children_unique initial control valid unique input) input
                    (chooseLatent initial control input).2 output
              | some label =>
                  simp only [selected] at support
                  rw [PMF.mem_support_map_iff] at support
                  obtain ⟨result, _, rfl⟩ := support
                  simpa only [selected] using finishLatent_children_unique _
                    (chooseLatent_children_unique initial control valid unique input) input
                    (chooseLatent initial control input).2 result.2

/-- Initial empty graphs retain unique incoming edges throughout the actual
interaction, using the existing allocation invariant rather than a new game. -/
theorem latent_run_children_unique {Result : Type} (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (supply : List Label) (nodup : supply.Nodup) (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentWorld initial terminal hashOracle)
      (LatentState.empty supply, ([], []))).support) : out.state.1.ChildrenUnique := by
  have invariant := Program.run_preserves
    (latentWorld initial terminal hashOracle)
    (fun state : LatentWorldState Payload Digest Label => state.1.AllocationValid ∧ state.1.ChildrenUnique)
    (by intro state valid request answer reachable
        exact ⟨(latent_step_allocation initial terminal state valid.1 request answer reachable).valid,
          latent_step_children_unique initial terminal state valid.1 valid.2 request answer reachable⟩)
    attack (LatentState.empty supply, ([], []))
    (by refine ⟨latent_empty_allocation supply nodup, ?_⟩; intro left member; cases member) out support
  exact invariant.2

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Publishing a selected coordinate preserves the relation if the published
input covers every incoming edge of that coordinate. Orphan coordinates are
allowed: the covering condition is then vacuous. -/
theorem LatentDataRelation.publish {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state) (input : CompressionInput Payload Digest)
    (label : Label) (covers : ∀ edge ∈ state.graph, edge.2 = label →
      latentDecodedEdge function edge = (input, function label)) :
    LatentDataRelation function full (finishLatent state input (some label) (function label)) := by
  refine ⟨relation.sound, relation.complete, ?_⟩
  intro edge member disclosed
  by_cases same : edge.2 = label
  · rw [covers edge member same]
    exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    apply relation.published edge member
    have distinct : (edge.2 == label) = false := by simp [same]
    simpa only [finishLatent, List.lookup_cons, distinct] using disclosed

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Unique incoming edges discharge the covering condition for publication of
an actual data edge. Only the executable finish operation is used. -/
theorem LatentDataRelation.publish_data {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state) (unique : state.ChildrenUnique)
    (parent : Digest ⊕ Label) (block : Payload) (label : Label)
    (member : ((parent, block), label) ∈ state.graph) :
    LatentDataRelation function full
      (finishLatent state (latentValue function parent, (false, block)) (some label) (function label)) := by
  apply relation.publish
  intro edge stored same
  have key := unique edge stored ((parent, block), label) member same
  simp [latentDecodedEdge, key, same]

/-- The same structural invariant holds for each fixed eager coordinate
function; the joint eager/lazy equality transports the actual final state. -/
theorem latent_eager_children_unique [Fintype Label] {Result : Type}
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup)
    (attack : Program (WorldInput Payload Digest) Digest Result) (function : Label → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function))
      (LatentState.empty supply, ([], []))).support) : out.state.1.ChildrenUnique := by
  have mixed : Program.resultState out ∈ ((uniform (Label → Digest)).bind (fun function =>
      (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function))
        (LatentState.empty supply, ([], []))).map Program.resultState)).support := by
    rw [PMF.mem_support_bind_iff]
    refine ⟨function, PMF.mem_support_uniformOfFintype function, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨out, support, rfl⟩
  rw [latent_eager_run, PMF.mem_support_map_iff] at mixed
  obtain ⟨lazyOut, reachable, same⟩ := mixed
  have unique := latent_run_children_unique initial terminal supply nodup attack lazyOut reachable
  have states : lazyOut.state = out.state := congrArg Prod.fst same
  rwa [states] at unique

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Registering a terminal compression row changes neither the set of data
edges nor their existing publication obligations. -/
theorem LatentDataRelation.terminal_row {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state) (value : Digest) (block : Payload) (output : Digest) :
    LatentDataRelation function (((value, (true, block)), output) :: full) state := by
  refine ⟨fun _ member => List.mem_cons_of_mem _ (relation.sound member), ?_, relation.published⟩
  intro entry member data
  rcases List.mem_cons.mp member with rfl | old
  · cases data
  · exact relation.complete entry old data

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- A public cached response with no new coordinate preserves the relation. -/
theorem LatentDataRelation.publish_none {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state) (input : CompressionInput Payload Digest)
    (output : Digest) : LatentDataRelation function full (finishLatent state input none output) :=
  ⟨relation.sound, relation.complete, fun edge member disclosed =>
    List.mem_cons_of_mem _ (relation.published edge member disclosed)⟩

omit [Fintype Digest] [Nonempty Digest] in
/-- The real executable choice and publication of a pending data vertex
preserve the relation; inverse-parent decoding identifies the public input. -/
theorem LatentDataRelation.publish_pending {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state) (unique : state.ChildrenUnique)
    (initial : Digest) (values : RandomOracle.TableValues function state.revealed)
    (value : Digest) (block : Payload) (label : Label)
    (known : state.graph.lookup (latentParent initial state value, block) = some label)
    (fresh : state.exposed.lookup (value, (false, block)) = none) :
    LatentDataRelation function full
      (finishLatent (chooseLatent initial state (value, (false, block))).1 (value, (false, block))
        (chooseLatent initial state (value, (false, block))).2 (function label)) := by
  rw [relation.choose_known initial values value block label known fresh]
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp known
  have member : ((latentParent initial state value, block), label) ∈ state.graph := by rw [same]; simp
  have published := relation.publish_data unique (latentParent initial state value) block label member
  simpa only [latentParent_value initial function state values value] using published

/-- A pending data vertex is revealed by the actual eager ideal interpreter.
The coordinate backend here is precisely the controller's revealed cache. -/
theorem latent_pending_data_execution (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (state : LatentState Payload Digest Label)
    (full : CompressionTable Payload Digest) (relation : LatentDataRelation function full state)
    (values : RandomOracle.TableValues function state.revealed)
    (hashes : RandomOracle.Table (List Payload) Digest) (value : Digest) (block : Payload) (label : Label)
    (known : state.graph.lookup (latentParent initial state value, block) = some label)
    (fresh : state.exposed.lookup (value, (false, block)) = none)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle
      (state, (hashes, state.revealed)) (.inr (value, (false, block))) =
      PMF.pure ((finishLatent state (value, (false, block)) (some label) (function label),
        (hashes, (label, function label) :: state.revealed)), function label) := by
  have choice := relation.choose_known initial values value block label known fresh
  have pending := relation.pending (latentParent initial state value) block label known
    (by simpa only [latentParent_value initial function state values value] using fresh)
  simp only [List.lookup_eq_findSome?, beq_iff_eq] at fresh pending
  simp [latentCoordinateWorld, Program.statefulOracle, latentProgram,
    List.lookup_eq_findSome?, beq_iff_eq, fresh, terminalMessage, choice, Program.run,
    Program.adaptOracle, latentContextRequest, RandomOracle.withContext,
    RandomOracle.eager, pending, PMF.pure_map]

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- A newly reserved orphan coordinate has no incoming graph edge to publish. -/
theorem LatentDataRelation.publish_orphan {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state) (input : CompressionInput Payload Digest)
    (label : Label) (unused : ∀ edge ∈ state.graph, edge.2 ≠ label) :
    LatentDataRelation function full (finishLatent state input (some label) (function label)) := by
  apply relation.publish
  intro edge member equal
  exact False.elim (unused edge member equal)

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Publishing the fixed coordinate value preserves agreement of all revealed
rows with the same function, independently of table-order and collisions. -/
theorem finishLatent_values (function : Label → Digest) (state : LatentState Payload Digest Label)
    (values : RandomOracle.TableValues function state.revealed)
    (input : CompressionInput Payload Digest) (label : Label) :
    RandomOracle.TableValues function
      (finishLatent state input (some label) (function label)).revealed := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | old
  · rfl
  · exact values entry old

/-- A fresh recognized terminal call of the actual real interpreter uses the
shared hash oracle and leaves its coordinate cache and number supply intact. -/
theorem coordinate_real_terminal_recognized (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (full : CompressionTable Payload Digest)
    (hashes : RandomOracle.Table (List Payload) Digest) (coordinates : RandomOracle.Table Label Digest)
    (supply : List Label) (flag : Bool) (input : CompressionInput Payload Digest) (message : List Payload)
    (fresh : full.lookup input = none)
    (recognized : terminalMessage initial terminal full input = some message)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld (RandomOracle.eager function) hashOracle)
      (full, ((supply, flag), (hashes, coordinates))) input =
      (hashOracle hashes message).map (fun answer =>
        (((input, answer.2) :: full, ((supply, flag), (answer.1, coordinates))), answer.2)) := by
  simp only [List.lookup_eq_findSome?, beq_iff_eq] at fresh
  simp [Program.statefulOracle, simulatorProgram, List.lookup_eq_findSome?, beq_iff_eq,
    fresh, recognized, Program.run, realCoordinateWorld_eq (hashOracle := hashOracle), PMF.map_bind, PMF.pure_map]
  rfl

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
/-- Publication cannot change the inverse-parent choice at any digest distinct
from the newly published coordinate. This isolates the alias event explicitly. -/
theorem latentParent_finish_away (initial : Digest) (function : Label → Digest)
    (state : LatentState Payload Digest Label) (input : CompressionInput Payload Digest)
    (label : Label) (value : Digest) (away : function label ≠ value) :
    latentParent initial (finishLatent state input (some label) (function label)) value =
      latentParent initial state value := by
  have distinct : (value == function label) = false := by simp [Ne.symm away]
  simp [latentParent, finishLatent, List.lookup_cons, distinct]

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
/-- Existing literal graph parents remain literal after publication unless the
newly published coordinate equals one of them. The excluded event still needs
its probability justification in the complete coupled interaction. -/
theorem finishLatent_literal_stable (initial : Digest) (function : Label → Digest)
    (state : LatentState Payload Digest Label) (input : CompressionInput Payload Digest) (label : Label)
    (stable : ∀ edge ∈ state.graph, ∀ literal, edge.1.1 = .inl literal →
      latentParent initial state literal = .inl literal)
    (away : ∀ edge ∈ state.graph, ∀ literal, edge.1.1 = .inl literal → function label ≠ literal) :
    ∀ edge ∈ (finishLatent state input (some label) (function label)).graph,
      ∀ literal, edge.1.1 = .inl literal →
        latentParent initial (finishLatent state input (some label) (function label)) literal = .inl literal := by
  intro edge member literal parent
  exact (latentParent_finish_away initial function state input label literal
    (away edge member literal parent)).trans (stable edge member literal parent)

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Revealing a previously reserved vertex does not consume another unused
label. The actual finish operation filters its label, which is already absent. -/
theorem finishLatent_supply_of_not_mem (state : LatentState Payload Digest Label)
    (input : CompressionInput Payload Digest) (label : Label) (output : Digest)
    (unused : label ∉ state.supply) :
    (finishLatent state input (some label) output).supply = state.supply := by
  apply List.filter_eq_self.mpr
  intro other member
  have distinct : other ≠ label := by intro equal; exact unused (equal ▸ member)
  simpa only [bne_iff_ne] using distinct

/-- Concrete paired execution of a pending data edge: the real full cache
already contains its answer, while the symbolic side publishes that coordinate.
Both supported transitions return the same value and preserve the data-table
relation and supply agreement, with any independent shared hash kernel. -/
theorem coordinate_pending_data_pair (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (state : LatentState Payload Digest Label)
    (full : CompressionTable Payload Digest) (relation : LatentDataRelation function full state)
    (consistent : RandomOracle.TableConsistent full) (allocation : state.AllocationValid)
    (unique : state.ChildrenUnique) (values : RandomOracle.TableValues function state.revealed)
    (realHashes idealHashes : RandomOracle.Table (List Payload) Digest)
    (realCoordinates : RandomOracle.Table Label Digest) (flag : Bool)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (value : Digest) (block : Payload) (label : Label)
    (known : state.graph.lookup (latentParent initial state value, block) = some label)
    (fresh : state.exposed.lookup (value, (false, block)) = none)
    (realAnswer : CoordinateRealState Payload Digest Label × Digest)
    (idealAnswer : LatentWorldState Payload Digest Label × Digest)
    (realSupport : realAnswer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function) hashOracle
      (full, ((state.supply, flag), (realHashes, realCoordinates))) (.inr (value, (false, block)))).support)
    (idealSupport : idealAnswer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle
      (state, (idealHashes, state.revealed)) (.inr (value, (false, block)))).support) :
    realAnswer.2 = idealAnswer.2 ∧
    LatentDataRelation function realAnswer.1.1 idealAnswer.1.1 ∧
    realAnswer.1.2.1.1 = idealAnswer.1.1.supply ∧
    realAnswer.1.2 = ((state.supply, flag), (realHashes, realCoordinates)) := by
  have fullKnown : full.lookup (value, (false, block)) = some (function label) := by
    simpa only [latentParent_value initial function state values value] using
      relation.known consistent (latentParent initial state value) block label known
  have realExecution : coordinateRealWorld initial terminal (RandomOracle.eager function) hashOracle
      (full, ((state.supply, flag), (realHashes, realCoordinates))) (.inr (value, (false, block))) =
      PMF.pure ((full, ((state.supply, flag), (realHashes, realCoordinates))), function label) := by
    unfold coordinateRealWorld Program.implementedOracle
    simp only [compressionCall, Program.run, coordinate_real_known initial terminal function full
      ((state.supply, flag), (realHashes, realCoordinates)) _ _ fullKnown hashOracle,
      PMF.pure_bind, PMF.pure_map, Program.resultState]
  rw [realExecution, PMF.mem_support_pure_iff] at realSupport
  subst realAnswer
  rw [latent_pending_data_execution initial terminal function state full relation values idealHashes
    value block label known fresh hashOracle, PMF.mem_support_pure_iff] at idealSupport
  subst idealAnswer
  refine ⟨rfl, ?_, ?_, rfl⟩
  · have published := relation.publish_pending unique initial values value block label known fresh
    simpa only [relation.choose_known initial values value block label known fresh] using published
  · obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp known
    have member : ((latentParent initial state value, block), label) ∈ state.graph := by rw [table]; simp
    exact (finishLatent_supply_of_not_mem state (value, (false, block)) label (function label)
      (allocation.2 _ member)).symm

/-- When the public data key is new in the symbolic graph, both concrete
worlds allocate the same next label. Public parent decoding is justified by
the existing no-hidden-guess and literal-stability conditions. Publication
preserves the full data relation, not only the returned digest. -/
theorem coordinate_fresh_data_pair (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (injective : Function.Injective function)
    (avoid : ∀ label, function label ≠ initial)
    (state : LatentState Payload Digest Label) (full : CompressionTable Payload Digest)
    (relation : LatentDataRelation function full state) (consistent : RandomOracle.TableConsistent full)
    (allocation : state.AllocationValid) (unique : state.ChildrenUnique) (freshSupply : state.FreshSupply)
    (values : RandomOracle.TableValues function state.revealed)
    (realHashes idealHashes : RandomOracle.Table (List Payload) Digest)
    (realCoordinates : RandomOracle.Table Label Digest) (flag : Bool)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (value : Digest) (block : Payload) (child : Label) (rest : List Label)
    (supply : state.supply = child :: rest)
    (privateFresh : realCoordinates.lookup child = none)
    (fresh : state.exposed.lookup (value, (false, block)) = none)
    (missing : state.graph.lookup (latentParent initial state value, block) = none)
    (noGuess : ∀ label, state.revealed.lookup label = none → function label ≠ value)
    (literalStable : ∀ edge ∈ state.graph, ∀ literal, edge.1.1 = .inl literal →
      latentParent initial state literal = .inl literal)
    (realAnswer : CoordinateRealState Payload Digest Label × Digest)
    (idealAnswer : LatentWorldState Payload Digest Label × Digest)
    (realSupport : realAnswer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function) hashOracle
      (full, ((state.supply, flag), (realHashes, realCoordinates))) (.inr (value, (false, block)))).support)
    (idealSupport : idealAnswer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle
      (state, (idealHashes, state.revealed)) (.inr (value, (false, block)))).support) :
    realAnswer.2 = idealAnswer.2 ∧
    LatentDataRelation function realAnswer.1.1 idealAnswer.1.1 ∧
    realAnswer.1.2.1.1 = idealAnswer.1.1.supply ∧
    RandomOracle.TableConsistent realAnswer.1.1 := by
  let parent := latentParent initial state value
  let reserved : LatentState Payload Digest Label :=
    {state with graph := ((parent, block), child) :: state.graph, supply := rest}
  have canonical := latentParent_canonical initial function injective state values avoid value noGuess literalStable
  have fullFresh : full.lookup (value, (false, block)) = none := by
    have missingReal := relation.fresh parent block
      (by intro edge member equal
          apply canonical edge member
          simpa only [parent, latentParent_value initial function state values value] using equal) missing
    simpa only [parent, latentParent_value initial function state values value] using missingReal
  have childMember : child ∈ state.supply := by rw [supply]; exact List.mem_cons_self
  have pending := freshSupply child childMember
  have realExecution : coordinateRealWorld initial terminal (RandomOracle.eager function) hashOracle
      (full, ((state.supply, flag), (realHashes, realCoordinates))) (.inr (value, (false, block))) =
      PMF.pure ((((value, (false, block)), function child) :: full,
        ((rest, flag), (realHashes, (child, function child) :: realCoordinates))), function child) := by
    unfold coordinateRealWorld Program.implementedOracle
    simp only [compressionCall, Program.run, supply,
      coordinate_real_data_fresh initial terminal function full realHashes realCoordinates child rest flag value block
        fullFresh privateFresh hashOracle, PMF.pure_bind, PMF.pure_map, Program.resultState]
  have choice : chooseLatent initial state (value, (false, block)) = (reserved, some child) := by
    simp only [chooseLatent, ↓reduceIte, missing, reserveLabel, supply]
    rfl
  have idealExecution : latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle
      (state, (idealHashes, state.revealed)) (.inr (value, (false, block))) =
      PMF.pure ((finishLatent reserved (value, (false, block)) (some child) (function child),
        (idealHashes, (child, function child) :: state.revealed)), function child) := by
    simp only [List.lookup_eq_findSome?, beq_iff_eq] at fresh pending
    simp [latentCoordinateWorld, Program.statefulOracle, latentProgram, List.lookup_eq_findSome?, beq_iff_eq,
      fresh, terminalMessage, choice, Program.run, Program.adaptOracle, latentContextRequest,
      RandomOracle.withContext, RandomOracle.eager, pending, PMF.pure_map]
  rw [realExecution, PMF.mem_support_pure_iff] at realSupport
  subst realAnswer
  rw [idealExecution, PMF.mem_support_pure_iff] at idealSupport
  subst idealAnswer
  have newRelation : LatentDataRelation function (((value, (false, block)), function child) :: full) reserved := by
    simpa only [reserved, parent, latentDecodedEdge, latentParent_value initial function state values value] using
      relation.reserve_edge parent block child rest pending
  have newUnique : reserved.ChildrenUnique := by
    simpa only [choice] using chooseLatent_children_unique initial state allocation unique (value, (false, block))
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have published := newRelation.publish_data newUnique parent block child (by exact List.mem_cons_self)
    simpa only [parent, latentParent_value initial function state values value] using published
  · have unused : child ∉ rest := (List.nodup_cons.mp (supply ▸ allocation.1)).1
    exact (finishLatent_supply_of_not_mem reserved (value, (false, block)) child (function child) unused).symm
  · exact RandomOracle.TableConsistent.cons consistent _ _ fullFresh

end Foundation.Hash

