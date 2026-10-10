import Foundation.Constructions.Hash.LatentLiterals
import Foundation.Constructions.Hash.LatentRecognition

/-! Actual multi-block data execution follows the symbolic reservation loop.
Private parents need coordinate separation, not a public-query no-guess
hypothesis. The compression interpreter and iteration are the existing ones.
The high call includes its terminal block. Public terminal branches and the
complete two-world coupling remain separate proof obligations. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

local instance dataLoopCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance dataLoopGraphBEq : BEq ((Digest ⊕ Label) × Payload) := instBEqOfDecidableEq
local instance dataLoopLabelBEq : BEq Label := instBEqOfDecidableEq

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
/-- Decoding cannot alias a graph parent to a private symbolic parent, provided
literal parents on both sides avoid all coordinates. Unlike public inverse
lookup, this does not require that the parent coordinate has been published. -/
theorem LatentState.LiteralAvoids.parent_canonical
    {function : Label → Digest} {state : LatentState Payload Digest Label}
    (separate : state.LiteralAvoids function) (injective : Function.Injective function)
    (parent : Digest ⊕ Label)
    (parentSafe : ∀ literal, parent = .inl literal → ∀ label, function label ≠ literal) :
    ∀ edge ∈ state.graph,
      latentValue function edge.1.1 = latentValue function parent → edge.1.1 = parent := by
  intro edge member equal
  cases chosen : edge.1.1 with
  | inl literal =>
      cases parent with
      | inl value =>
          have same : literal = value := by simpa only [chosen, latentValue, Sum.elim_inl, id_eq] using equal
          exact congrArg Sum.inl same
      | inr label =>
          have same : literal = function label := by
            simpa only [chosen, latentValue, Sum.elim_inl, Sum.elim_inr, id_eq] using equal
          exact False.elim (separate edge member literal chosen label same.symm)
  | inr label =>
      cases parent with
      | inl value =>
          have same : function label = value := by
            simpa only [chosen, latentValue, Sum.elim_inl, Sum.elim_inr, id_eq] using equal
          exact False.elim (parentSafe value rfl label same)
      | inr other =>
          exact congrArg Sum.inr (injective (by simpa only [chosen, latentValue, Sum.elim_inr] using equal))

omit [Fintype Digest] [Nonempty Digest] in
/-- The same separation also supplies the existing decoded-graph consistency
lemma's key-injectivity premise. No probabilistic independence is asserted. -/
theorem LatentState.LiteralAvoids.decoded_consistent
    {function : Label → Digest} {state : LatentState Payload Digest Label}
    (separate : state.LiteralAvoids function) (injective : Function.Injective function)
    (consistent : RandomOracle.TableConsistent state.graph) :
    RandomOracle.TableConsistent (latentDecodedGraph function state) := by
  apply latentDecodedGraph_consistent function state consistent
  intro left leftMem right rightMem equal
  apply Prod.ext
  · exact separate.parent_canonical injective right.1.1
      (fun literal selected label => separate right rightMem literal selected label)
      left leftMem (congrArg Prod.fst equal)
  · exact congrArg (fun input => input.2.2) equal

/-- An actual internal data step does not touch the hash cache or overflow
flag. Every unused label remains absent from the private coordinate cache.
The symbolic and real supplies start equal and are proved to remain equal. -/
theorem latentAdvance_real_backend_frame (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (function : Label → Digest) (state : LatentState Payload Digest Label)
    (full : CompressionTable Payload Digest)
    (hashes : RandomOracle.Table (List Payload) Digest) (coordinates : RandomOracle.Table Label Digest)
    (flag : Bool) (relation : LatentDataRelation function full state)
    (consistent : RandomOracle.TableConsistent full) (nodup : state.supply.Nodup)
    (privateFresh : ∀ label ∈ state.supply, coordinates.lookup label = none)
    (available : state.supply ≠ []) (parent : Digest ⊕ Label) (block : Payload)
    (canonical : ∀ edge ∈ state.graph,
      latentValue function edge.1.1 = latentValue function parent → edge.1.1 = parent)
    (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld (RandomOracle.eager function) hashOracle)
      (full, ((state.supply, flag), (hashes, coordinates)))
      (latentValue function parent, (false, block))).support) :
    answer.1.2.1.1 = (latentAdvance initial state parent block).1.supply ∧
    answer.1.2.1.2 = flag ∧ answer.1.2.2.1 = hashes ∧
    ∀ label ∈ (latentAdvance initial state parent block).1.supply,
      answer.1.2.2.2.lookup label = none := by
  cases known : state.graph.lookup (parent, block) with
  | some child =>
      rw [coordinate_real_known initial terminal function full _ _ _
        (relation.known consistent parent block child known) hashOracle,
        PMF.mem_support_pure_iff] at support
      subst answer
      simpa only [latentAdvance, known] using
        (show state.supply = state.supply ∧ flag = flag ∧ hashes = hashes ∧
          ∀ label ∈ state.supply, coordinates.lookup label = none from ⟨rfl, rfl, rfl, privateFresh⟩)
  | none =>
      have missing := relation.fresh parent block canonical known
      cases supply : state.supply with
      | nil => exact False.elim (available supply)
      | cons child rest =>
          have member : child ∈ state.supply := by rw [supply]; exact List.mem_cons_self
          rw [supply, coordinate_real_data_fresh initial terminal function full hashes coordinates
            child rest flag _ block missing (privateFresh child member) hashOracle,
            PMF.mem_support_pure_iff] at support
          subst answer
          simp only [latentAdvance, known, reserveLabel, supply]
          refine ⟨True.intro, True.intro, True.intro, ?_⟩
          intro label inRest
          have different : label ≠ child := by
            intro equal
            have distinct : (child :: rest).Nodup := supply ▸ nodup
            exact (List.nodup_cons.mp distinct).1 (equal ▸ inRest)
          have old := privateFresh label (by rw [supply]; exact List.mem_cons_of_mem _ inRest)
          simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true,
            ↓reduceIte] using old

/-- The existing data-compression iteration, with the actual full-table
interpreter, follows every symbolic reservation over a whole message. Capacity
is consumed per block; no nonempty supply is assumed after the last block.
The conclusion retains both table correspondence and the actual endpoint path,
as well as the private coordinate freshness needed by the next operation. -/
theorem reserveMessage_real_data_loop (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (function : Label → Digest) (injective : Function.Injective function)
    (avoid : ∀ label, function label ≠ initial)
    (message : List Payload) (state : LatentState Payload Digest Label)
    (full : CompressionTable Payload Digest)
    (hashes : RandomOracle.Table (List Payload) Digest) (coordinates : RandomOracle.Table Label Digest)
    (flag : Bool) (relation : LatentDataRelation function full state)
    (consistent : RandomOracle.TableConsistent full) (allocation : state.AllocationValid)
    (freshSupply : state.FreshSupply) (separate : state.LiteralAvoids function)
    (privateFresh : ∀ label ∈ state.supply, coordinates.lookup label = none)
    (noOverflow : state.overflow = false) (available : message.length ≤ state.supply.length)
    (parent : Digest ⊕ Label)
    (parentSafe : ∀ literal, parent = .inl literal → ∀ label, function label ≠ literal)
    (out : Outcome (CompressionInput Payload Digest) Digest Digest (CoordinateRealState Payload Digest Label))
    (support : out ∈ ((iterate (latentValue function parent) (message.map (fun block => (false, block)))).run
      (Program.statefulOracle (simulatorProgram initial terminal)
        (realCoordinateWorld (RandomOracle.eager function) hashOracle))
      (full, ((state.supply, flag), (hashes, coordinates)))).support) :
    LatentDataRelation function out.state.1 (reserveMessage initial state parent message) ∧
    RandomOracle.TableConsistent out.state.1 ∧
    out.state.2.1.1 = (reserveMessage initial state parent message).supply ∧
    out.state.2.1.2 = flag ∧ out.state.2.2.1 = hashes ∧
    (∀ label ∈ (reserveMessage initial state parent message).supply,
      out.state.2.2.2.lookup label = none) ∧
    DataChain (latentValue function parent)
      (latentDecodedGraph function (reserveMessage initial state parent message)) message out.result := by
  induction message generalizing state full hashes coordinates flag parent out with
  | nil =>
      simp only [List.map_nil, iterate, Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact ⟨relation, consistent, rfl, rfl, rfl, privateFresh, .nil⟩
  | cons block rest ih =>
      simp only [List.map_cons, iterate, Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, firstSupport, tailSupport⟩ := support
      rw [PMF.mem_support_map_iff] at tailSupport
      obtain ⟨tail, tailSupport, rfl⟩ := tailSupport
      have nonempty : state.supply ≠ [] := by
        intro empty
        simp only [List.length_cons, empty, List.length_nil] at available
        omega
      have canonical := separate.parent_canonical injective parent parentSafe
      have first := latentAdvance_real_step initial terminal function state full hashes coordinates flag
        relation consistent freshSupply privateFresh nonempty parent block canonical answer firstSupport
      have backend := latentAdvance_real_backend_frame initial terminal function state full hashes coordinates flag
        relation consistent allocation.1 privateFresh nonempty parent block canonical answer firstSupport
      have allocated := latentAdvance_allocation initial state allocation parent block
      have remaining : rest.length ≤ (latentAdvance initial state parent block).1.supply.length := by
        have := allocated.length
        simp only [List.length_cons] at available
        omega
      have nextOverflow : (latentAdvance initial state parent block).1.overflow = false :=
        (allocated.overflow (by simp only [List.length_cons] at available; omega)).trans noOverflow
      have nextFresh := (latentAdvance_frame initial state parent block).freshSupply freshSupply
      have nextSeparate := latentAdvance_literal_avoids initial function state separate parent block parentSafe
      have nextSafe := latentAdvance_parent_safe initial function avoid state parent block
      have sameState : answer.1 =
          (answer.1.1, (((latentAdvance initial state parent block).1.supply, flag),
            (hashes, answer.1.2.2.2))) :=
        Prod.ext rfl (Prod.ext (Prod.ext backend.1 backend.2.1) (Prod.ext backend.2.2.1 rfl))
      have nextSupport : tail ∈ ((iterate (latentValue function (latentAdvance initial state parent block).2)
          (rest.map (fun value => (false, value)))).run
        (Program.statefulOracle (simulatorProgram initial terminal)
          (realCoordinateWorld (RandomOracle.eager function) hashOracle))
        (answer.1.1, (((latentAdvance initial state parent block).1.supply, flag),
          (hashes, answer.1.2.2.2)))).support := by
        rw [first.2.2.1, sameState] at tailSupport
        exact tailSupport
      have last := ih (latentAdvance initial state parent block).1 answer.1.1 hashes answer.1.2.2.2 flag
        first.1 first.2.1 allocated.valid nextFresh nextSeparate backend.2.2.2 nextOverflow remaining
        (latentAdvance initial state parent block).2 nextSafe tail nextSupport
      refine ⟨last.1, last.2.1, last.2.2.1, last.2.2.2.1, last.2.2.2.2.1, last.2.2.2.2.2.1, ?_⟩
      have edge := latentAdvance_decoded_edge initial function state parent block nextOverflow
      have finalEdge := latentDecodedGraph_mono function
        (reserveMessage_graph_subset initial (latentAdvance initial state parent block).1
          (latentAdvance initial state parent block).2 rest) edge
      have start : DataChain (latentValue function parent)
          (latentDecodedGraph function (reserveMessage initial state parent (block :: rest))) [block]
          (latentValue function (latentAdvance initial state parent block).2) :=
        .snoc block .nil finalEdge
      simpa only [List.singleton_append] using start.append last.2.2.2.2.2.2

/-- Data-only execution under the existing full-table interpreter preserves
terminal coverage outside chronological graph failure. Arbitrary backends are
allowed: supported full tables project to the existing compression semantics.
Old terminal rows cannot acquire a new data prefix under the no-late-chain
lemma. This is a support invariant, not equality of backend probabilities. -/
theorem simulator_data_terminal_consistent {Backend : Type}
    (backend : Oracle (SimulatorRequest Payload) Digest Backend)
    (initial : Digest) (terminal : Payload) (message : List Payload)
    (full : CompressionTable Payload Digest) (hashes : RandomOracle.Table (List Payload) Digest)
    (state : Backend) (covered : TerminalConsistent initial terminal full hashes)
    (out : Outcome (CompressionInput Payload Digest) Digest Digest (CompressionTable Payload Digest × Backend))
    (support : out ∈ ((iterate initial (message.map (fun block => (false, block)))).run
      (Program.statefulOracle (simulatorProgram initial terminal) backend) (full, state)).support)
    (good : ForwardFresh initial out.state.1) :
    TerminalConsistent initial terminal out.state.1 hashes := by
  have projected := simulator_run_support backend initial terminal full state _ out support
  intro blocks target output chain member
  have old := iterate_data_terminal_old initial message full (Program.mapState Prod.fst out)
    projected _ member rfl
  obtain ⟨later, extended⟩ := RandomOracle.run_table_extends
    (iterate initial (message.map (fun block => (false, block)))) full
    (Program.mapState Prod.fst out) projected
  change out.state.1 = later ++ full at extended
  rw [extended] at chain good
  exact covered blocks target output
    (no_late_chain_append later full (target, (true, terminal)) output old good chain) old

/-- A whole actual data-prefix execution followed by its terminal compression
returns the fixed hash function's message value. Coverage before the prefix and
chronological freshness after it justify the cached-terminal case; a new
terminal is recognized from the actual path and calls the same hash function.
No equality of the real and ideal hash caches is required. -/
theorem coordinate_real_data_terminal_value
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (hashFunction : List Payload → Digest) (message : List Payload)
    (full : CompressionTable Payload Digest)
    (backend : RealCoordinateState Payload Digest Label)
    (covered : TerminalConsistent initial terminal full backend.2.1)
    (hashValues : RandomOracle.TableValues hashFunction backend.2.1)
    (first : Outcome (CompressionInput Payload Digest) Digest Digest (CoordinateRealState Payload Digest Label))
    (firstSupport : first ∈ ((iterate initial (message.map (fun block => (false, block)))).run
      (Program.statefulOracle (simulatorProgram initial terminal)
        (realCoordinateWorld (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
      (full, backend)).support)
    (hashSame : first.state.2.2.1 = backend.2.1)
    (good : ForwardFresh initial first.state.1)
    (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld (RandomOracle.eager function) (RandomOracle.eager hashFunction))
      first.state (first.result, (true, terminal))).support) :
    answer.2 = hashFunction message ∧
    answer.1.2.1 = first.state.2.1 ∧ answer.1.2.2.2 = first.state.2.2.2 ∧
    RandomOracle.TableValues hashFunction answer.1.2.2.1 := by
  have coverage := simulator_data_terminal_consistent
    (realCoordinateWorld (RandomOracle.eager function) (RandomOracle.eager hashFunction))
    initial terminal message full backend.2.1 backend covered first firstSupport good
  have projected := simulator_run_support
    (realCoordinateWorld (RandomOracle.eager function) (RandomOracle.eager hashFunction))
    initial terminal full backend _ first firstSupport
  have path := iterate_data_chain initial message full (Program.mapState Prod.fst first) projected
  have values : RandomOracle.TableValues hashFunction first.state.2.2.1 := by rwa [hashSame]
  cases cached : first.state.1.lookup (first.result, (true, terminal)) with
  | some output =>
      obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp cached
      have member : ((first.result, (true, terminal)), output) ∈ first.state.1 := by rw [table]; simp
      have registered := coverage message first.result output path member
      have value := hashValues.lookup registered
      rw [coordinate_real_known initial terminal function first.state.1 first.state.2 _ output cached
        (RandomOracle.eager hashFunction), PMF.mem_support_pure_iff] at support
      subst answer
      exact ⟨value, rfl, rfl, values⟩
  | none =>
      obtain ⟨injective, avoid⟩ := freshOutputs_graph good.outputs
      have recognized : terminalMessage initial terminal first.state.1 (first.result, (true, terminal)) = some message := by
        simp only [terminalMessage, and_self, ↓reduceIte]
        exact messagePrefix_complete injective avoid path
      have execution := coordinate_real_terminal_recognized initial terminal function first.state.1
        first.state.2.2.1 first.state.2.2.2 first.state.2.1.1 first.state.2.1.2 _ message cached recognized
        (RandomOracle.eager hashFunction)
      have sameState : first.state = (first.state.1, ((first.state.2.1.1, first.state.2.1.2),
          (first.state.2.2.1, first.state.2.2.2))) := rfl
      rw [sameState, execution, PMF.mem_support_map_iff] at support
      obtain ⟨response, reachable, rfl⟩ := support
      have result := RandomOracle.eager_step_values hashFunction first.state.2.2.1 values message response reachable
      exact ⟨result.2, rfl, rfl, result.1⟩

/-- A terminal-marked real transition cannot add a data edge. Reusing the
actual compression support also covers a cached terminal without a table
update. The symbolic graph and its publication obligations stay unchanged. -/
theorem LatentDataRelation.terminal_transition
    {function : Label → Digest} {full : CompressionTable Payload Digest}
    {state : LatentState Payload Digest Label} (relation : LatentDataRelation function full state)
    (input : CompressionInput Payload Digest) (marked : input.2.1 = true)
    (answer : CompressionTable Payload Digest × Digest)
    (support : answer ∈ (RandomOracle.oracle full input).support) :
    LatentDataRelation function answer.1 state := by
  refine ⟨fun _ member => RandomOracle.step_table_subset full input answer support (relation.sound member),
    ?_, relation.published⟩
  intro entry member data
  rcases List.mem_cons.mp (RandomOracle.step_entries full input answer support member) with new | old
  · subst entry
    rw [marked] at data
    cases data
  · exact relation.complete entry old data

/-- A supported high-level call at the original real interface follows the
symbolic reservation of the entire message and returns the shared fixed hash
function's value. These are explicit state-relation hypotheses, to be maintained
by the eventual two-world coupling; this is not an assumed security bound. -/
theorem coordinate_real_high_step
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (injective : Function.Injective function) (avoid : ∀ label, function label ≠ initial)
    (hashFunction : List Payload → Digest) (message : List Payload)
    (state : LatentState Payload Digest Label) (full : CompressionTable Payload Digest)
    (hashes : RandomOracle.Table (List Payload) Digest) (coordinates : RandomOracle.Table Label Digest)
    (flag : Bool) (relation : LatentDataRelation function full state)
    (consistent : RandomOracle.TableConsistent full) (allocation : state.AllocationValid)
    (freshSupply : state.FreshSupply) (separate : state.LiteralAvoids function)
    (privateFresh : ∀ label ∈ state.supply, coordinates.lookup label = none)
    (noOverflow : state.overflow = false) (available : message.length ≤ state.supply.length)
    (covered : TerminalConsistent initial terminal full hashes)
    (hashValues : RandomOracle.TableValues hashFunction hashes)
    (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function)
      (RandomOracle.eager hashFunction) (full, ((state.supply, flag), (hashes, coordinates)))
      (.inl message)).support)
    (good : ForwardFresh initial answer.1.1) :
    answer.2 = hashFunction message ∧
    LatentDataRelation function answer.1.1 (reserveMessage initial state (.inl initial) message) ∧
    RandomOracle.TableConsistent answer.1.1 ∧
    answer.1.2.1.1 = (reserveMessage initial state (.inl initial) message).supply ∧
    answer.1.2.1.2 = flag ∧ RandomOracle.TableValues hashFunction answer.1.2.2.1 ∧
    ∀ label ∈ (reserveMessage initial state (.inl initial) message).supply,
      answer.1.2.2.2.lookup label = none := by
  unfold coordinateRealWorld Program.implementedOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, rfl⟩ := support
  change out ∈ ((prefixFreeMD initial terminal message).run
    (Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
    (full, ((state.supply, flag), (hashes, coordinates)))).support at reachable
  rw [prefixFreeMD, encode, iterate_append, Program.run_bind, PMF.mem_support_bind_iff] at reachable
  obtain ⟨first, firstSupport, lastSupport⟩ := reachable
  rw [PMF.mem_support_map_iff] at lastSupport
  obtain ⟨last, lastSupport, rfl⟩ := lastSupport
  simp only [iterate, Program.run, PMF.pure_map] at lastSupport
  rw [PMF.mem_support_bind_iff] at lastSupport
  obtain ⟨response, terminalSupport, returned⟩ := lastSupport
  rw [PMF.mem_support_pure_iff] at returned
  subst last
  have terminalProjected := simulator_step_support
    (realCoordinateWorld (RandomOracle.eager function) (RandomOracle.eager hashFunction))
    initial terminal first.state.1 first.state.2 (first.result, (true, terminal)) response terminalSupport
  obtain ⟨later, extended⟩ := RandomOracle.step_table_extends first.state.1
    (first.result, (true, terminal)) (response.1.1, response.2) terminalProjected
  have firstGood : ForwardFresh initial first.state.1 := by
    change ForwardFresh initial response.1.1 at good
    rw [extended] at good
    exact RandomOracle.Avoided.append_tail later first.state.1 good
  have data := reserveMessage_real_data_loop initial terminal function injective avoid message state
    full hashes coordinates flag relation consistent allocation freshSupply separate privateFresh
    noOverflow available (.inl initial) (by intro literal selected; cases selected; exact avoid) first firstSupport
  have value := coordinate_real_data_terminal_value initial terminal function hashFunction message full
    ((state.supply, flag), (hashes, coordinates)) covered hashValues first firstSupport
    data.2.2.2.2.1 firstGood response terminalSupport
  refine ⟨value.1, data.1.terminal_transition _ rfl _ terminalProjected,
    RandomOracle.step_table_consistent _ data.2.1 _ _ terminalProjected, ?_, ?_, value.2.2.2, ?_⟩
  · exact (congrArg Prod.fst value.2.1).trans data.2.2.1
  · exact (congrArg Prod.snd value.2.1).trans data.2.2.2.1
  · intro label member
    change response.1.2.2.2.lookup label = none
    rw [value.2.2.1]
    exact data.2.2.2.2.2.1 label member

/-- The actual symbolic high call uses only the hash window. Coordinates are
untouched even when their kernel is a fixed function rather than lazy sampling. -/
theorem latent_coordinate_high_execution (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentState Payload Digest Label)
    (hashes : RandomOracle.Table (List Payload) Digest) (table : RandomOracle.Table Label Digest)
    (message : List Payload) :
    latentCoordinateWorld initial terminal coordinates hashOracle (state, (hashes, table)) (.inl message) =
      (hashOracle hashes message).map (fun answer =>
        ((reserveMessage initial state (.inl initial) message, (answer.1, table)), answer.2)) := by
  simp [latentCoordinateWorld, Program.statefulOracle, latentProgram, Program.run,
    Program.adaptOracle, latentContextRequest, RandomOracle.withContext, simulatorBackend,
    PMF.map_bind, PMF.pure_map, PMF.map_comp, Function.comp_def]
  rfl

/-- The concrete high-query case of the paired worlds: every supported pair
returns the same value and retains the real/full-to-symbolic data relation.
The two hash caches may differ; each merely agrees with the shared function.
The low-query cases and whole-interaction invariant are still required. -/
theorem coordinate_high_pair
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (injective : Function.Injective function) (avoid : ∀ label, function label ≠ initial)
    (hashFunction : List Payload → Digest) (message : List Payload)
    (state : LatentState Payload Digest Label) (full : CompressionTable Payload Digest)
    (realHashes idealHashes : RandomOracle.Table (List Payload) Digest)
    (realCoordinates idealCoordinates : RandomOracle.Table Label Digest) (flag : Bool)
    (relation : LatentDataRelation function full state)
    (consistent : RandomOracle.TableConsistent full) (allocation : state.AllocationValid)
    (freshSupply : state.FreshSupply) (separate : state.LiteralAvoids function)
    (privateFresh : ∀ label ∈ state.supply, realCoordinates.lookup label = none)
    (noOverflow : state.overflow = false) (available : message.length ≤ state.supply.length)
    (covered : TerminalConsistent initial terminal full realHashes)
    (realValues : RandomOracle.TableValues hashFunction realHashes)
    (idealValues : RandomOracle.TableValues hashFunction idealHashes)
    (realAnswer : CoordinateRealState Payload Digest Label × Digest)
    (idealAnswer : LatentWorldState Payload Digest Label × Digest)
    (realSupport : realAnswer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function)
      (RandomOracle.eager hashFunction) (full, ((state.supply, flag), (realHashes, realCoordinates)))
      (.inl message)).support)
    (idealSupport : idealAnswer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      (RandomOracle.eager hashFunction) (state, (idealHashes, idealCoordinates)) (.inl message)).support)
    (good : ForwardFresh initial realAnswer.1.1) :
    realAnswer.2 = idealAnswer.2 ∧
    LatentDataRelation function realAnswer.1.1 idealAnswer.1.1 ∧
    realAnswer.1.2.1.1 = idealAnswer.1.1.supply ∧
    RandomOracle.TableConsistent realAnswer.1.1 ∧
    (∀ label ∈ idealAnswer.1.1.supply, realAnswer.1.2.2.2.lookup label = none) := by
  have realStep := coordinate_real_high_step initial terminal function injective avoid hashFunction message state full
    realHashes realCoordinates flag relation consistent allocation freshSupply separate privateFresh noOverflow
    available covered realValues realAnswer realSupport good
  rw [latent_coordinate_high_execution, PMF.mem_support_map_iff] at idealSupport
  obtain ⟨response, reachable, rfl⟩ := idealSupport
  have idealStep := RandomOracle.eager_step_values hashFunction idealHashes idealValues message response reachable
  exact ⟨realStep.1.trans idealStep.2.symm, realStep.2.1, realStep.2.2.2.1,
    realStep.2.2.1, realStep.2.2.2.2.2.2⟩

end Foundation.Hash
