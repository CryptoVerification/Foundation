import Foundation.Constructions.Hash.OracleWorlds

/-! Complete-chain invariants for the marker-terminal simulator.
These are deterministic graph facts corresponding to the chain uniqueness
argument in CSF 2012, Section V. No collision probability is assumed here.
-/
namespace Foundation.Hash

variable {Payload Digest : Type} [DecidableEq Payload] [DecidableEq Digest]

/-- A path from the initial value using only marked data blocks. The terminal
compression call is separate, so this path describes exactly a message prefix. -/
inductive DataChain (initial : Digest) (table : CompressionTable Payload Digest) :
    List Payload → Digest → Prop where
  | nil : DataChain initial table [] initial
  | snoc {blocks : List Payload} {previous target : Digest} (block : Payload)
      (chain : DataChain initial table blocks previous)
      (edge : ((previous, (false, block)), target) ∈ table) :
      DataChain initial table (blocks ++ [block]) target

def OutputInjective (table : CompressionTable Payload Digest) : Prop :=
  ∀ left ∈ table, ∀ right ∈ table, left.2 = right.2 → left.1 = right.1

def AvoidInitial (initial : Digest) (table : CompressionTable Payload Digest) : Prop :=
  ∀ entry ∈ table, entry.2 ≠ initial

omit [DecidableEq Payload] [DecidableEq Digest] in
theorem dataEdges_mem (table : CompressionTable Payload Digest)
    (previous target : Digest) (block : Payload) :
    (target, (previous, block)) ∈ dataEdges table ↔
      ((previous, (false, block)), target) ∈ table := by
  simp only [dataEdges, List.mem_filterMap]
  constructor
  · rintro ⟨⟨⟨p, marker, b⟩, t⟩, hm, he⟩
    cases marker <;> simp at he
    rcases he with ⟨rfl, rfl, rfl⟩
    exact hm
  · intro hm
    exact ⟨((previous, (false, block)), target), hm, rfl⟩

private theorem mem_of_lookup {α β : Type} [DecidableEq α]
    {table : List (α × β)} {key : α} {value : β}
    (h : table.lookup key = some value) : (key, value) ∈ table := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp h
  rw [he]
  simp

omit [DecidableEq Payload] in
/-- A successful backwards search returns a genuine data chain, with length
bounded by the supplied fuel. This statement needs no injectivity assumption. -/
theorem messagePrefix_sound (initial : Digest) (table : CompressionTable Payload Digest)
    (fuel : Nat) (target : Digest) (blocks : List Payload)
    (h : messagePrefix initial table fuel target = some blocks) :
    DataChain initial table blocks target ∧ blocks.length ≤ fuel := by
  induction fuel generalizing target blocks with
  | zero =>
      simp only [messagePrefix] at h
      split at h
      · rename_i he
        subst target
        cases Option.some.inj h
        exact ⟨.nil, Nat.le_refl 0⟩
      · cases h
  | succ fuel ih =>
      simp only [messagePrefix] at h
      split at h
      · rename_i he
        subst target
        cases Option.some.inj h
        exact ⟨.nil, Nat.zero_le _⟩
      · split at h
        · cases h
        · rename_i previous block he
          obtain ⟨xs, hx, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨hc, hl⟩ := ih previous xs hx
          refine ⟨.snoc block hc ?_, ?_⟩
          · exact (dataEdges_mem table previous target block).mp (mem_of_lookup he)
          · simp only [List.length_append, List.length_singleton]
            omega

omit [DecidableEq Payload] [DecidableEq Digest] in
/-- Outside output collisions and returns to the initial value, the endpoint
uniquely determines a data chain. This includes empty versus nonempty chains. -/
theorem DataChain.unique {initial : Digest} {table : CompressionTable Payload Digest}
    (injective : OutputInjective table) (avoid : AvoidInitial initial table)
    {left right : List Payload} {target : Digest}
    (hl : DataChain initial table left target) (hr : DataChain initial table right target) :
    left = right := by
  induction hl generalizing right with
  | nil =>
      cases hr with
      | nil => rfl
      | snoc block chain edge => exact False.elim (avoid _ edge rfl)
  | @snoc blocks previous target block chain edge ih =>
      cases hr with
      | nil => exact False.elim (avoid _ edge rfl)
      | @snoc otherBlocks otherPrevious _ otherBlock otherChain otherEdge =>
          have he := injective _ edge _ otherEdge rfl
          have hp : previous = otherPrevious := congrArg Prod.fst he
          have hb : block = otherBlock := congrArg (fun input => input.2.2) he
          subst otherPrevious
          subst otherBlock
          exact congrArg (fun xs => xs ++ [block]) (ih otherChain)

omit [DecidableEq Payload] in
/-- Injective compression outputs give the reverse lookup used by the actual
simulator, rather than just an existential predecessor. -/
theorem dataEdges_lookup {table : CompressionTable Payload Digest}
    (injective : OutputInjective table) {previous target : Digest} {block : Payload}
    (edge : ((previous, (false, block)), target) ∈ table) :
    (dataEdges table).lookup target = some (previous, block) := by
  have hm := (dataEdges_mem table previous target block).mpr edge
  cases he : (dataEdges table).lookup target with
  | none =>
      have hn := List.lookup_eq_none_iff.mp he (target, (previous, block)) hm
      simp at hn
  | some value =>
      obtain ⟨p, b⟩ := value
      have hm' := (dataEdges_mem table p target b).mp (mem_of_lookup he)
      have hv := injective _ hm' _ edge rfl
      have hp : p = previous := congrArg Prod.fst hv
      have hb : b = block := congrArg (fun input => input.2.2) hv
      subst p
      subst b
      rfl

omit [DecidableEq Payload] in
/-- Under the graph invariant, the executable backwards search finds every
chain that fits its fuel, including chains assembled by adaptive low-level calls. -/
theorem DataChain.search {initial : Digest} {table : CompressionTable Payload Digest}
    (injective : OutputInjective table) (avoid : AvoidInitial initial table)
    {blocks : List Payload} {target : Digest}
    (chain : DataChain initial table blocks target) (fuel : Nat) (bound : blocks.length ≤ fuel) :
    messagePrefix initial table fuel target = some blocks := by
  induction chain generalizing fuel with
  | nil => cases fuel <;> simp [messagePrefix]
  | @snoc blocks previous target block chain edge ih =>
      have ht : target ≠ initial := avoid _ edge
      cases fuel with
      | zero => simp at bound
      | succ fuel =>
          have hb : blocks.length ≤ fuel := by
            simp only [List.length_append, List.length_singleton] at bound
            omega
          simp only [messagePrefix, ht, ↓reduceIte, dataEdges_lookup injective edge]
          rw [ih fuel hb]
          rfl

omit [DecidableEq Payload] [DecidableEq Digest] in
/-- Reachable data chains visit distinct output vertices. Each visited vertex
has an earlier prefix witness, which rules out a cycle by chain uniqueness. -/
private theorem DataChain.endpoints {initial : Digest} {table : CompressionTable Payload Digest}
    (injective : OutputInjective table) (avoid : AvoidInitial initial table)
    {blocks : List Payload} {target : Digest} (chain : DataChain initial table blocks target) :
    ∃ vertices : List Digest, vertices.length = blocks.length ∧ vertices.Nodup ∧
      ∀ vertex ∈ vertices, vertex ∈ table.map Prod.snd ∧
        ∃ xs : List Payload, xs.length ≤ blocks.length ∧ DataChain initial table xs vertex := by
  induction chain with
  | nil => exact ⟨[], rfl, List.nodup_nil, by simp⟩
  | @snoc blocks previous target block chain edge ih =>
      obtain ⟨vertices, hv, hn, hw⟩ := ih
      have hnot : target ∉ vertices := by
        intro hm
        obtain ⟨_, xs, hx, hc⟩ := hw target hm
        have he := hc.unique injective avoid (.snoc block chain edge)
        have hl := congrArg List.length he
        simp only [List.length_append, List.length_singleton] at hl
        omega
      refine ⟨target :: vertices, ?_, List.nodup_cons.mpr ⟨hnot, hn⟩, ?_⟩
      · simp [hv]
      · intro vertex hm
        rcases List.mem_cons.mp hm with he | hm
        · subst vertex
          refine ⟨List.mem_map.mpr ⟨_, edge, rfl⟩, blocks ++ [block], le_rfl,
            .snoc block chain edge⟩
        · obtain ⟨ht, xs, hx, hc⟩ := hw vertex hm
          refine ⟨ht, xs, ?_, hc⟩
          simp only [List.length_append, List.length_singleton]
          omega

omit [DecidableEq Payload] [DecidableEq Digest] in
/-- The table length used as fuel by the simulator suffices for every data
chain under the graph invariant. No independent maximum message length is needed
for this search lemma; resource and distinguishing bounds still need limits. -/
theorem DataChain.length_le {initial : Digest} {table : CompressionTable Payload Digest}
    (injective : OutputInjective table) (avoid : AvoidInitial initial table)
    {blocks : List Payload} {target : Digest} (chain : DataChain initial table blocks target) :
    blocks.length ≤ table.length := by
  obtain ⟨vertices, hv, hn, hw⟩ := chain.endpoints injective avoid
  have hsubset : vertices ⊆ table.map Prod.snd := fun vertex hm => (hw vertex hm).1
  have hl := hn.length_le_of_subset hsubset
  simpa only [hv, List.length_map] using hl

omit [DecidableEq Payload] in
theorem messagePrefix_complete {initial : Digest} {table : CompressionTable Payload Digest}
    (injective : OutputInjective table) (avoid : AvoidInitial initial table)
    {blocks : List Payload} {target : Digest} (chain : DataChain initial table blocks target) :
    messagePrefix initial table table.length target = some blocks :=
  chain.search injective avoid table.length (chain.length_le injective avoid)


omit [DecidableEq Payload] [DecidableEq Digest] in
/-- Every path remains valid when more graph edges become available. -/
theorem DataChain.mono {initial : Digest}
    {before after : CompressionTable Payload Digest} (includes : before ⊆ after)
    {blocks : List Payload} {target : Digest} (chain : DataChain initial before blocks target) :
    DataChain initial after blocks target := by
  induction chain with
  | nil => exact .nil
  | snoc block chain edge ih => exact .snoc block ih (includes edge)

omit [DecidableEq Payload] [DecidableEq Digest] in
/-- Concatenate a prefix path with a path starting at its endpoint. -/
theorem DataChain.append {initial middle target : Digest}
    {table : CompressionTable Payload Digest} {left right : List Payload}
    (headChain : DataChain initial table left middle) (tailChain : DataChain middle table right target) :
    DataChain initial table (left ++ right) target := by
  induction tailChain with
  | nil => simpa using headChain
  | snoc block chain edge ih =>
      simpa only [List.append_assoc] using DataChain.snoc block ih edge

/-- For a fixed message, coherent compression storage determines one endpoint.
Output collisions are allowed; this is distinct from backwards uniqueness. -/
theorem DataChain.forward_unique {initial : Digest} {table : CompressionTable Payload Digest}
    (consistent : CryptoOracle.RandomOracle.TableConsistent table)
    {blocks : List Payload} {left right : Digest}
    (hl : DataChain initial table blocks left) (hr : DataChain initial table blocks right) :
    left = right := by
  have compare {xs : List Payload} {first : Digest} (firstChain : DataChain initial table xs first) :
      ∀ {ys : List Payload} {second : Digest}, DataChain initial table ys second →
        xs = ys → first = second := by
    induction firstChain with
    | nil =>
        intro ys second secondChain same
        cases secondChain with
        | nil => rfl
        | snoc block chain edge => simp at same
    | @snoc xs previous first block chain edge ih =>
        intro ys second secondChain same
        cases secondChain with
        | nil => simp at same
        | @snoc otherBlocks otherPrevious otherTarget otherBlock otherChain otherEdge =>
            obtain ⟨he, hb⟩ := List.append_inj' same (by simp : [block].length = [otherBlock].length)
            have hb' : block = otherBlock := List.singleton_inj.mp hb
            subst otherBlock
            have hp := ih otherChain he
            subst otherPrevious
            exact consistent.functional edge otherEdge
  exact compare hl hr rfl

/-- The shared terminal recognizer returns only well-marked complete data
paths. It does not inspect any ideal-hash record. -/
theorem terminalMessage_sound (initial : Digest) (terminal : Payload)
    (table : CompressionTable Payload Digest) (input : CompressionInput Payload Digest)
    (message : List Payload) (recognized : terminalMessage initial terminal table input = some message) :
    input = (input.1, (true, terminal)) ∧ DataChain initial table message input.1 := by
  unfold terminalMessage at recognized
  split at recognized
  · rename_i marker
    refine ⟨?_, (messagePrefix_sound initial table table.length input.1 message recognized).1⟩
    rcases input with ⟨previous, marked, block⟩
    simp only [Prod.mk.injEq] at marker ⊢
    exact ⟨trivial, marker⟩
  · cases recognized

end Foundation.Hash
