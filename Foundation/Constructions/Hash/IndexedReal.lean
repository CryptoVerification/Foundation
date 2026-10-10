import Foundation.Constructions.Hash.TrackedReal
import Foundation.Crypto.Semantics.Oracle.IndexedRandomOracle

/-! Chronological output labels in the actual hash experiment. Internal hash
calls allocate labels. Public compression responses and the final response of
each high-level hash call mark their labels exposed.
Erasure is exact for the existing tracked real experiment. This is the indexing
step toward CSF 2012's latent-value experiments; it does not by itself make
internally sampled values independent of the attacker's observations. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Result : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

local instance indexedCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq

structure IndexedRealState (Payload Digest : Type) where
  compression : RandomOracle.IndexedTable (CompressionInput Payload Digest) Digest
  exposed : CompressionTable Payload Digest
  hashes : RandomOracle.Table (List Payload) Digest
  guessed : Bool
  published : List Nat

def IndexedRealState.empty : IndexedRealState Payload Digest := ⟨⟨[], []⟩, [], [], false, []⟩

def IndexedRealState.erase (initial : Digest) (state : IndexedRealState Payload Digest) :
    TrackedRealState Payload Digest :=
  ⟨state.compression.erase initial, state.exposed, state.hashes, state.guessed⟩

/-- Publication records a chronological coordinate, without returning the
coordinate to the attacker. Repeated requests may repeat a publication record. -/
def publishIndex (compression : RandomOracle.IndexedTable (CompressionInput Payload Digest) Digest)
    (input : CompressionInput Payload Digest) (published : List Nat) : List Nat :=
  (compression.labels.lookup input).toList ++ published

/-- A high-level hash exposes its final compression response, not its entire
internal trace. The actual last query supplies the chronological coordinate. -/
def publishLast (compression : RandomOracle.IndexedTable (CompressionInput Payload Digest) Digest)
    (trace : List (CompressionInput Payload Digest × Digest)) (published : List Nat) : List Nat :=
  match trace.getLast? with
  | some entry => publishIndex compression entry.1 published
  | none => published

omit [Fintype Digest] [Nonempty Digest] in
theorem publishIndex_valid
    (compression : RandomOracle.IndexedTable (CompressionInput Payload Digest) Digest)
    (valid : compression.Valid) (input : CompressionInput Payload Digest) (published : List Nat)
    (previous : ∀ label ∈ published, label < compression.values.length) :
    ∀ label ∈ publishIndex compression input published, label < compression.values.length := by
  cases recorded : compression.labels.lookup input with
  | none => simpa only [publishIndex, recorded, Option.toList_none, List.nil_append] using previous
  | some index =>
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp recorded
      have member : (input, index) ∈ compression.labels := by rw [he]; simp
      intro label hm
      simp only [publishIndex, recorded, Option.toList_some, List.singleton_append, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact valid (input, label) member
      · exact previous label hm

noncomputable def indexedRealWorld (initial : Digest) (terminal : Payload) :
    Oracle (WorldInput Payload Digest) Digest (IndexedRealState Payload Digest) :=
  fun state request => match request with
  | .inl message =>
      ((prefixFreeMD initial terminal message).run (RandomOracle.IndexedTable.oracle initial) state.compression).map
        (fun out => (⟨out.state, state.exposed, rememberHash state.hashes message out.result,
          state.guessed, publishLast out.state out.trace state.published⟩, out.result))
  | .inr input =>
      (RandomOracle.IndexedTable.oracle initial state.compression input).map (fun answer =>
        (⟨answer.1, rememberPublic state.exposed input answer.2,
          recordLowHash initial terminal (state.erase initial) input answer.2,
          markHiddenGuess (state.erase initial) input,
          publishIndex answer.1 input state.published⟩, answer.2))

/-- Label allocation remains well formed through both hash interfaces. -/
theorem indexedReal_step_valid (initial : Digest) (terminal : Payload)
    (state : IndexedRealState Payload Digest) (valid : state.compression.Valid)
    (request : WorldInput Payload Digest) (answer : IndexedRealState Payload Digest × Digest)
    (support : answer ∈ (indexedRealWorld initial terminal state request).support) :
    answer.1.compression.Valid := by
  cases request with
  | inl message =>
      rw [indexedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, ho, rfl⟩ := support
      exact RandomOracle.IndexedTable.run_valid initial (prefixFreeMD initial terminal message) state.compression valid out ho
  | inr input =>
      rw [indexedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, hr, rfl⟩ := support
      exact RandomOracle.IndexedTable.step_valid initial state.compression valid input response hr

/-- Erasing chronological coordinates preserves the actual tracked transition,
including its raw exposed table, message registration and guess flag. -/
theorem indexedReal_step_erase (initial : Digest) (terminal : Payload)
    (state : IndexedRealState Payload Digest) (valid : state.compression.Valid)
    (request : WorldInput Payload Digest) :
    (indexedRealWorld initial terminal state request).map
      (fun answer => (answer.1.erase initial, answer.2)) =
    trackedRealWorld initial terminal (state.erase initial) request := by
  cases request with
  | inl message =>
      have h := congrArg (PMF.map (fun out : Outcome (CompressionInput Payload Digest) Digest Digest
          (CompressionTable Payload Digest) =>
          ((⟨out.state, state.exposed, rememberHash state.hashes message out.result, state.guessed⟩,
            out.result) : TrackedRealState Payload Digest × Digest)))
        (RandomOracle.IndexedTable.run_erase initial (prefixFreeMD initial terminal message) state.compression valid)
      simpa only [indexedRealWorld, trackedRealWorld, IndexedRealState.erase,
        PMF.map_comp, Program.mapState, Function.comp_def] using h
  | inr input =>
      have h := congrArg (PMF.map (fun answer : CompressionTable Payload Digest × Digest =>
          ((⟨answer.1, rememberPublic state.exposed input answer.2,
            recordLowHash initial terminal (state.erase initial) input answer.2,
            markHiddenGuess (state.erase initial) input⟩, answer.2) : TrackedRealState Payload Digest × Digest)))
        (RandomOracle.IndexedTable.step_erase initial state.compression valid input)
      simpa only [indexedRealWorld, trackedRealWorld, IndexedRealState.erase,
        PMF.map_comp, Function.comp_def] using h

/-- No result, public transcript, shared hash record, or real guess flag changes
when the chronological labels are introduced into an adaptive interaction. -/
theorem indexedReal_run_erase (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : IndexedRealState Payload Digest) (valid : state.compression.Valid) :
    (attack.run (indexedRealWorld initial terminal) state).map
      (Program.mapState (IndexedRealState.erase initial)) =
    attack.run (trackedRealWorld initial terminal) (state.erase initial) :=
  Program.run_state_map_of_invariant (IndexedRealState.erase initial)
    (indexedRealWorld initial terminal) (trackedRealWorld initial terminal)
    (fun state => state.compression.Valid) (indexedReal_step_valid initial terminal)
    (indexedReal_step_erase initial terminal) attack state valid

/-- The indexed experiment inherits the already proved complete-terminal
invariant. Indexing introduces no new security assumption. -/
theorem indexedReal_terminal_from_empty (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (IndexedRealState Payload Digest))
    (support : out ∈ (attack.run (indexedRealWorld initial terminal) IndexedRealState.empty).support)
    (good : ForwardFresh initial (out.state.compression.erase initial)) (noGuess : out.state.guessed = false) :
    TerminalConsistent initial terminal (out.state.compression.erase initial) out.state.hashes := by
  have erased : Program.mapState (IndexedRealState.erase initial) out ∈
      ((attack.run (indexedRealWorld initial terminal) IndexedRealState.empty).map
        (Program.mapState (IndexedRealState.erase initial))).support :=
    by rw [PMF.mem_support_map_iff]; exact ⟨out, support, rfl⟩
  rw [indexedReal_run_erase initial terminal attack IndexedRealState.empty
    (by intro entry hm; cases hm)] at erased
  exact trackedReal_terminal_from_empty initial terminal attack _ erased good noGuess

/-- Every publication record refers to an allocated chronological value. -/
def IndexedRealState.PublicValid (state : IndexedRealState Payload Digest) : Prop :=
  ∀ label ∈ state.published, label < state.compression.values.length

theorem indexedReal_step_public_valid (initial : Digest) (terminal : Payload)
    (state : IndexedRealState Payload Digest) (valid : state.compression.Valid)
    (publicValid : state.PublicValid) (request : WorldInput Payload Digest)
    (answer : IndexedRealState Payload Digest × Digest)
    (support : answer ∈ (indexedRealWorld initial terminal state request).support) :
    answer.1.PublicValid := by
  cases request with
  | inl message =>
      rw [indexedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨out, ho, rfl⟩ := support
      obtain ⟨added, extended, _⟩ := RandomOracle.IndexedTable.run_values_extend initial
        (prefixFreeMD initial terminal message) state.compression out ho
      have afterValid := RandomOracle.IndexedTable.run_valid initial (prefixFreeMD initial terminal message)
        state.compression valid out ho
      have previous : ∀ label ∈ state.published, label < out.state.values.length := by
        intro label member
        have earlier := publicValid label member
        simp only [extended, List.length_append]
        omega
      change ∀ label ∈ publishLast out.state out.trace state.published, label < out.state.values.length
      unfold publishLast
      split
      · exact publishIndex_valid out.state afterValid _ state.published previous
      · exact previous
  | inr input =>
      rw [indexedRealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨response, hr, rfl⟩ := support
      obtain ⟨label, records, value⟩ := RandomOracle.IndexedTable.step_records initial state.compression valid input response hr
      obtain ⟨added, extended, _⟩ := RandomOracle.IndexedTable.step_values_extend initial state.compression input response hr
      intro publicLabel member
      simp only [publishIndex, records, Option.toList_some, List.singleton_append, List.mem_cons] at member
      rcases member with rfl | member
      · exact (List.getElem?_eq_some_iff.mp value).choose
      · have previous := publicValid publicLabel member
        simp only [extended, List.length_append]
        omega

/-- The entire indexed interaction preserves storage and publication validity. -/
theorem indexedReal_run_valid (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : IndexedRealState Payload Digest) (valid : state.compression.Valid)
    (publicValid : state.PublicValid)
    (out : Outcome (WorldInput Payload Digest) Digest Result (IndexedRealState Payload Digest))
    (support : out ∈ (attack.run (indexedRealWorld initial terminal) state).support) :
    out.state.compression.Valid ∧ out.state.PublicValid := by
  apply Program.run_preserves (indexedRealWorld initial terminal)
    (fun state => state.compression.Valid ∧ state.PublicValid) _ attack state ⟨valid, publicValid⟩ out support
  intro state valid request answer support
  exact ⟨indexedReal_step_valid initial terminal state valid.1 request answer support,
    indexedReal_step_public_valid initial terminal state valid.1 valid.2 request answer support⟩

/-- Every public compression response publishes its genuine stored coordinate.
The label is proof state; the adversary receives only the digest response. -/
theorem indexedReal_low_publishes (initial : Digest) (terminal : Payload)
    (state : IndexedRealState Payload Digest) (valid : state.compression.Valid)
    (input : CompressionInput Payload Digest) (answer : IndexedRealState Payload Digest × Digest)
    (support : answer ∈ (indexedRealWorld initial terminal state (.inr input)).support) :
    ∃ label, label ∈ answer.1.published ∧ answer.1.compression.labels.lookup input = some label ∧
      answer.1.compression.values[label]? = some answer.2 := by
  rw [indexedRealWorld, PMF.mem_support_map_iff] at support
  obtain ⟨response, hr, rfl⟩ := support
  obtain ⟨label, records, value⟩ := RandomOracle.IndexedTable.step_records initial state.compression valid input response hr
  exact ⟨label, by simp [publishIndex, records], records, value⟩

/-- The number of stored indexed values includes internal compression calls.
A q-call interaction with at most blockLimit encoded blocks per call allocates
at most q*blockLimit values. This is not a machine-space or time bound. -/
theorem indexedReal_bounded_values {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (initial : Digest) (terminal : Payload)
    (state : IndexedRealState Payload Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (IndexedRealState Payload Digest))
    (support : out ∈ (attack.run (indexedRealWorld initial terminal) state).support) :
    out.state.compression.values.length ≤ state.compression.values.length + q * blockLimit := by
  induction bound generalizing state out with
  | done result q =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      change state.compression.values.length ≤ state.compression.values.length + q * blockLimit
      omega
  | coin next q bound ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state out ht
  | hash message next q length bound ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      have remaining := ih answer.2 answer.1 tail ht
      rw [indexedRealWorld, PMF.mem_support_map_iff] at ha
      obtain ⟨first, hf, rfl⟩ := ha
      have step := RandomOracle.IndexedTable.bounded_values initial
        (prefixFreeMD_queries initial terminal message) state.compression first hf
      simp only [Nat.add_mul, one_mul] at *
      change tail.state.compression.values.length ≤ state.compression.values.length + (q * blockLimit + blockLimit)
      change tail.state.compression.values.length ≤ first.state.values.length + q * blockLimit at remaining
      omega
  | compression input next q positive bound ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      have remaining := ih answer.2 answer.1 tail ht
      rw [indexedRealWorld, PMF.mem_support_map_iff] at ha
      obtain ⟨first, hf, rfl⟩ := ha
      obtain ⟨added, extended, count⟩ := RandomOracle.IndexedTable.step_values_extend initial state.compression input first hf
      simp only [Nat.add_mul, one_mul]
      change tail.state.compression.values.length ≤ state.compression.values.length + (q * blockLimit + blockLimit)
      change tail.state.compression.values.length ≤ first.1.values.length + q * blockLimit at remaining
      rw [extended, List.length_append] at remaining
      omega

/-- A high-level response publishes its terminal coordinate as well. A
terminal hash value is therefore never classified as hidden merely because its
compression input was not requested through the public low-level window. -/
theorem indexedReal_high_publishes (initial : Digest) (terminal : Payload)
    (state : IndexedRealState Payload Digest) (valid : state.compression.Valid)
    (message : List Payload) (answer : IndexedRealState Payload Digest × Digest)
    (support : answer ∈ (indexedRealWorld initial terminal state (.inl message)).support) :
    ∃ label, label ∈ answer.1.published ∧ answer.1.compression.values[label]? = some answer.2 := by
  rw [indexedRealWorld, PMF.mem_support_map_iff] at support
  obtain ⟨out, ho, rfl⟩ := support
  obtain ⟨target, last⟩ := prefixFreeMD_last_query (RandomOracle.IndexedTable.oracle initial)
    initial terminal message state.compression out ho
  have member : ((target, (true, terminal)), out.result) ∈ out.trace := by
    obtain ⟨before, he⟩ := List.getLast?_eq_some_iff.mp last
    rw [he]
    simp
  obtain ⟨label, records, value⟩ := RandomOracle.IndexedTable.run_response_label initial
    (prefixFreeMD initial terminal message) state.compression valid out ho _ _ member
  exact ⟨label, by simp [publishLast, last, publishIndex, records], value⟩

end Foundation.Hash
