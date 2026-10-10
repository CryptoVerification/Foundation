import Foundation.Constructions.Hash.OracleWorlds

/-! Secret-prefix MAC games using Foundation's existing oracle interpreter.
Unlike EncryptThenMAC.Semantics.MAC.sign, tagging here is an oracle computation
with state shared with public hash queries. The existing deterministic MAC
interface cannot represent that state without fixing an entire hash function.
This module specifies the game and admissibility; it does not prove unforgeability.
-/
namespace Foundation.Symmetric.SecretPrefixMAC

open CryptoOracle Foundation.Probability
open scoped ENNReal

abbrev Key (κ : Nat) := Bits κ
abbrev Message (κ : Nat) := List (Bits κ)
abbrev Tag (n : Nat) := Bits n
abbrev Request (κ : Nat) := Message κ ⊕ Message κ
abbrev Attack (κ n : Nat) := Program (Request κ) (Tag n) (Message κ × Tag n)

/-- The fixed-width key is a single payload block. No length field is used. -/
def input {κ : Nat} (key : Key κ) (message : Message κ) : Message κ := key :: message

noncomputable def keygen (κ : Nat) : ProbComp (Key κ) := uniform (Key κ)

noncomputable def tag {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ)
    (state : State) (message : Message κ) : ProbComp (State × Tag n) :=
  hash state (input key message)

noncomputable def verify {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ)
    (state : State) (message : Message κ) (candidate : Tag n) : ProbComp (State × Bool) :=
  (tag hash key state message).map fun answer => (answer.1, decide (answer.2 = candidate))

/-- The left interface is public hashing; the right interface is tagging.
Both call the same hash state. Only tagging updates the list of signed messages. -/
noncomputable def oracle {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ) :
    Oracle (Request κ) (Tag n) (State × List (Message κ)) :=
  fun (state, signed) request => match request with
    | .inl message => (hash state message).map fun answer => ((answer.1, signed), answer.2)
    | .inr message => (tag hash key state message).map fun answer =>
        ((answer.1, message :: signed), answer.2)

/-- A single adaptive adversary retains its state throughout. Final verification
is one additional hash call. The winning message must be fresh and in the domain. -/
noncomputable def game {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (initial : State)
    (messageLimit : Nat) (attack : Attack κ n) : ProbComp Bool :=
  (keygen κ).bind fun key =>
    (attack.run (oracle hash key) (initial, [])).bind fun outcome =>
      (verify hash key outcome.state.1 outcome.result.1 outcome.result.2).map fun answer =>
        answer.2 && decide (outcome.result.1 ∉ outcome.state.2) &&
          decide (outcome.result.1.length ≤ messageLimit)

noncomputable def romGame {κ n : Nat} (messageLimit : Nat) (attack : Attack κ n) :
    ProbComp Bool := game RandomOracle.oracle [] messageLimit attack

noncomputable def successProbability {κ n : Nat} (messageLimit : Nat)
    (attack : Attack κ n) : ℝ≥0∞ := eventProb (romGame messageLimit attack) (· = true)

/-- Separate budgets are needed: the existing BoundedQueries counts both
interfaces together and does not constrain input lengths. All branches are
bounded, including choices made adaptively from responses and local coins. -/
inductive Budget {κ n : Nat} (hashLength messageLength : Nat) :
    Attack κ n → Nat → Nat → Prop where
  | done (result : Message κ × Tag n) (qH qT : Nat) :
      Budget hashLength messageLength (.done result) qH qT
  | hash (message : Message κ) (next : Tag n → Attack κ n) (qH qT : Nat)
      (length : message.length ≤ hashLength)
      (bound : ∀ response, Budget hashLength messageLength (next response) qH qT) :
      Budget hashLength messageLength (.query (.inl message) next) (qH + 1) qT
  | sign (message : Message κ) (next : Tag n → Attack κ n) (qH qT : Nat)
      (length : message.length ≤ messageLength)
      (bound : ∀ response, Budget hashLength messageLength (next response) qH qT) :
      Budget hashLength messageLength (.query (.inr message) next) qH (qT + 1)
  | coin (next : Bool → Attack κ n) (qH qT : Nat)
      (bound : ∀ bit, Budget hashLength messageLength (next bit) qH qT) :
      Budget hashLength messageLength (.coin next) qH qT

theorem Budget.queries {κ n hashLength messageLength qH qT : Nat} {attack : Attack κ n}
    (h : Budget hashLength messageLength attack qH qT) :
    attack.BoundedQueries (qH + qT) := by
  induction h with
  | done result qH qT => exact .done _ _
  | hash message next qH qT hl hb ih =>
      simpa only [Nat.add_right_comm] using
        Program.BoundedQueries.query (.inl message) next (qH + qT) ih
  | sign message next qH qT hl hb ih =>
      simpa only [Nat.add_assoc] using
        Program.BoundedQueries.query (.inr message) next (qH + qT) ih
  | coin next qH qT hb ih => exact .coin next (qH + qT) ih

/-- The separate syntactic budgets bound the actual public hash and signing
transcripts, for any shared oracle state and any adaptive responses. -/
theorem Budget.trace_counts {κ n hashLength messageLength qH qT : Nat}
    {attack : Attack κ n} (h : Budget hashLength messageLength attack qH qT)
    {State : Type} (handler : Oracle (Request κ) (Tag n) State) (state : State)
    (outcome : Outcome (Request κ) (Tag n) (Message κ × Tag n) State)
    (hs : outcome ∈ (attack.run handler state).support) :
    outcome.trace.countP (fun e => e.1.isLeft) ≤ qH ∧
      outcome.trace.countP (fun e => e.1.isRight) ≤ qT := by
  induction h generalizing state outcome with
  | done result qH qT =>
      rw [Program.run, PMF.mem_support_pure_iff] at hs
      subst outcome
      simp
  | hash message next qH qT hl hb ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at hs
      obtain ⟨answer, _, hs⟩ := hs
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨tail, ht, rfl⟩ := hs
      obtain ⟨hh, ht⟩ := ih answer.2 answer.1 tail ht
      simp only [List.countP_cons]
      exact And.intro (Nat.succ_le_succ hh) ht
  | sign message next qH qT hl hb ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at hs
      obtain ⟨answer, _, hs⟩ := hs
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨tail, ht, rfl⟩ := hs
      obtain ⟨hh, ht⟩ := ih answer.2 answer.1 tail ht
      simp only [List.countP_cons]
      exact And.intro hh (Nat.succ_le_succ ht)
  | coin next qH qT hb ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at hs
      obtain ⟨bit, _, hs⟩ := hs
      exact ih bit state outcome hs

/-- Tagging followed by verification uses the saved value, for every possible
response of the lazy random oracle and every previously shared table. -/
theorem rom_correct {κ n : Nat} (key : Key κ) (message : Message κ)
    (table : RandomOracle.Table (Message κ) (Tag n))
    (answer : RandomOracle.Table (Message κ) (Tag n) × Tag n)
    (h : answer ∈ (tag RandomOracle.oracle key table message).support) :
    verify RandomOracle.oracle key answer.1 message answer.2 =
      PMF.pure (answer.1, true) := by
  have hs := (RandomOracle.step table (input key message) answer h).1
  simp [verify, tag, RandomOracle.known _ _ _ hs, PMF.pure_map]

/-- A MAC message of L payload blocks requires L+2 compression calls:
one key block and one terminal block are included. -/
theorem constructed_tag_queries {κ n : Nat} (initial : Bits n) (terminal : Bits κ)
    (key : Key κ) (message : Message κ) :
    (Foundation.Hash.prefixFreeMD initial terminal (input key message)).BoundedQueries
      (message.length + 2) := by
  simpa [input, Nat.add_assoc] using
    Foundation.Hash.prefixFreeMD_queries initial terminal (input key message)

end Foundation.Symmetric.SecretPrefixMAC
