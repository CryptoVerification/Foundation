import Foundation.Constructions.Hash.GraphFreshness

/-! Private-chain consistency of the concrete simulator. Under the data-edge exposure-order condition on private
tables, every completed private chain ending at a terminal entry agrees with
the shared ideal hash. This invariant alone does not relate hidden real chains
to private chains and is not the final indifferentiability theorem. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

local instance : BEq (List Payload) := instBEqOfDecidableEq

def TerminalConsistent (initial : Digest) (terminal : Payload)
    (table : CompressionTable Payload Digest)
    (idealTable : RandomOracle.Table (List Payload) Digest) : Prop :=
  ∀ blocks target output, DataChain initial table blocks target →
    ((target, (true, terminal)), output) ∈ table → idealTable.lookup blocks = some output

omit [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem TerminalConsistent.empty (initial : Digest) (terminal : Payload)
    (idealTable : RandomOracle.Table (List Payload) Digest) :
    TerminalConsistent initial terminal [] idealTable := by
  intro blocks target output chain entry
  simp at entry

omit [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem TerminalConsistent.mono_ideal {initial : Digest} {terminal : Payload}
    {table : CompressionTable Payload Digest}
    {before after : RandomOracle.Table (List Payload) Digest}
    (consistent : TerminalConsistent initial terminal table before)
    (keeps : ∀ blocks output, before.lookup blocks = some output →
      after.lookup blocks = some output) : TerminalConsistent initial terminal table after := by
  intro blocks target output chain entry
  exact keeps blocks output (consistent blocks target output chain entry)

omit [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Extending a chronological table preserves old complete terminal chains.
Only the new terminal entry, when complete already, needs an ideal-hash answer. -/
theorem TerminalConsistent.extend {initial : Digest} {terminal : Payload}
    {table : CompressionTable Payload Digest}
    {before after : RandomOracle.Table (List Payload) Digest}
    {newInput : CompressionInput Payload Digest} {newOutput : Digest}
    (consistent : TerminalConsistent initial terminal table before)
    (good : DataForwardFresh initial ((newInput, newOutput) :: table))
    (keeps : ∀ blocks output, before.lookup blocks = some output →
      after.lookup blocks = some output)
    (newTerminal : ∀ blocks target, newInput = (target, (true, terminal)) →
      DataChain initial table blocks target → after.lookup blocks = some newOutput) :
    TerminalConsistent initial terminal ((newInput, newOutput) :: table) after := by
  intro blocks target output chain entry
  rcases List.mem_cons.mp entry with he | he
  · have hi : newInput = (target, (true, terminal)) := (congrArg Prod.fst he).symm
    have ho : output = newOutput := congrArg Prod.snd he
    subst output
    apply newTerminal blocks target hi
    exact chain.remove_terminal (by simp only [hi])
  · have oldChain := data_no_late_chain good he chain
    exact keeps blocks output (consistent blocks target output oldChain he)

/-- The actual low-level simulator preserves terminal consistency outside the
chronological graph failure. The ideal random-oracle table is shared, and old
assignments are retained throughout the step. -/
theorem simulator_preserves_terminal {initial : Digest} {terminal : Payload}
    {table : CompressionTable Payload Digest}
    {idealTable : RandomOracle.Table (List Payload) Digest}
    (consistent : TerminalConsistent initial terminal table idealTable)
    (input : CompressionInput Payload Digest)
    (answer : (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest) × Digest)
    (support : answer ∈ (compressionSimulator RandomOracle.oracle initial terminal
      (table, idealTable) input).support)
    (good : DataForwardFresh initial answer.1.1) :
    TerminalConsistent initial terminal answer.1.1 answer.1.2 := by
  rw [compressionSimulator_eq] at support
  cases ht : table.lookup input with
  | some output =>
      simp only [ht, PMF.mem_support_pure_iff] at support
      subst answer
      exact consistent
  | none =>
      simp only [ht] at support
      by_cases terminalInput : input.2.1 = true ∧ input.2.2 = terminal
      · simp only [terminalInput, and_self, ↓reduceIte] at support
        cases found : messagePrefix initial table table.length input.1 with
        | some message =>
            simp only [found, PMF.mem_support_map_iff] at support
            obtain ⟨idealAnswer, hi, rfl⟩ := support
            obtain ⟨records, keeps, _⟩ := RandomOracle.step idealTable message idealAnswer hi
            apply consistent.extend good keeps
            intro blocks target he chain
            have hg : DataForwardFresh initial table := good.2
            obtain ⟨injective, avoid⟩ := freshOutputs_graph hg.outputs
            have hc : DataChain initial table message input.1 :=
              (messagePrefix_sound initial table table.length input.1 message found).1
            have htarg : input.1 = target := congrArg Prod.fst he
            rw [htarg] at hc
            have hm := chain.unique injective avoid hc
            rw [hm]
            exact records
        | none =>
            simp only [found, PMF.mem_support_map_iff] at support
            obtain ⟨output, _, rfl⟩ := support
            apply consistent.extend good (fun _ _ h => h)
            intro blocks target he chain
            have hg : DataForwardFresh initial table := good.2
            obtain ⟨injective, avoid⟩ := freshOutputs_graph hg.outputs
            have htarg : input.1 = target := congrArg Prod.fst he
            have complete := messagePrefix_complete injective avoid chain
            rw [htarg] at found
            rw [complete] at found
            cases found
      · simp only [terminalInput, ↓reduceIte, PMF.mem_support_map_iff] at support
        obtain ⟨output, _, rfl⟩ := support
        apply consistent.extend good (fun _ _ h => h)
        intro blocks target he chain
        subst input
        exact False.elim (terminalInput ⟨rfl, rfl⟩)

theorem ideal_step_private_extends {initial : Digest} {terminal : Payload}
    (table : CompressionTable Payload Digest)
    (idealTable : RandomOracle.Table (List Payload) Digest)
    (request : WorldInput Payload Digest)
    (answer : (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest) × Digest)
    (support : answer ∈ (idealWorld RandomOracle.oracle initial terminal
      (table, idealTable) request).support) :
    ∃ later : CompressionTable Payload Digest, answer.1.1 = later ++ table := by
  cases request with
  | inl message =>
      rw [idealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨hashAnswer, _, rfl⟩ := support
      exact ⟨[], rfl⟩
  | inr input =>
      rcases simulator_step RandomOracle.oracle initial terminal table idealTable input answer support with
        he | he
      · exact ⟨[], he⟩
      · exact ⟨[(input, answer.2)], he⟩

/-- High-level queries and low-level simulation share the same ideal table.
Both preserve the completed-private-chain invariant whenever the resulting
chronological private table satisfies the graph condition. -/
theorem ideal_step_preserves_terminal {initial : Digest} {terminal : Payload}
    {table : CompressionTable Payload Digest}
    {idealTable : RandomOracle.Table (List Payload) Digest}
    (consistent : TerminalConsistent initial terminal table idealTable)
    (request : WorldInput Payload Digest)
    (answer : (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest) × Digest)
    (support : answer ∈ (idealWorld RandomOracle.oracle initial terminal
      (table, idealTable) request).support)
    (good : DataForwardFresh initial answer.1.1) :
    TerminalConsistent initial terminal answer.1.1 answer.1.2 := by
  cases request with
  | inl message =>
      rw [idealWorld, PMF.mem_support_map_iff] at support
      obtain ⟨hashAnswer, hh, rfl⟩ := support
      exact consistent.mono_ideal (RandomOracle.step idealTable message hashAnswer hh).2.1
  | inr input => exact simulator_preserves_terminal consistent input answer support good

/-- Arbitrary adaptive executions retain the private table as a chronological
suffix and preserve terminal consistency outside the final graph failure.
This is a full shared-state invariant, not just a per-query response equation. -/
theorem ideal_run_terminal {Result : Type} {initial : Digest} {terminal : Payload}
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (table : CompressionTable Payload Digest)
    (idealTable : RandomOracle.Table (List Payload) Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result
      (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest))
    (support : out ∈ (attack.run (idealWorld RandomOracle.oracle initial terminal)
      (table, idealTable)).support) :
    (∃ later : CompressionTable Payload Digest, out.state.1 = later ++ table) ∧
    (TerminalConsistent initial terminal table idealTable →
      DataForwardFresh initial out.state.1 → TerminalConsistent initial terminal out.state.1 out.state.2) := by
  induction attack generalizing table idealTable out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact ⟨⟨[], rfl⟩, fun h _ => h⟩
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, support⟩ := support
      exact ih bit table idealTable out support
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, support⟩ := support
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨tail, ht, rfl⟩ := support
      obtain ⟨⟨later, he⟩, hc⟩ := ih answer.2 answer.1.1 answer.1.2 tail ht
      obtain ⟨added, hs⟩ := ideal_step_private_extends table idealTable request answer ha
      refine ⟨⟨later ++ added, ?_⟩, ?_⟩
      · simp only
        rw [he, hs, List.append_assoc]
      · intro consistent good
        have hgood : DataForwardFresh initial answer.1.1 := by
          apply RandomOracle.Avoided.append_tail later answer.1.1
          rw [← he]
          exact good
        exact hc (ideal_step_preserves_terminal consistent request answer ha hgood) good

/-- Starting empty, every complete private terminal chain agrees with the
ideal hash throughout arbitrary adaptive access to both public interfaces. -/
theorem ideal_run_from_empty {Result : Type} (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result
      (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest))
    (support : out ∈ (attack.run (idealWorld RandomOracle.oracle initial terminal) ([], [])).support)
    (good : DataForwardFresh initial out.state.1) :
    TerminalConsistent initial terminal out.state.1 out.state.2 :=
  (ideal_run_terminal attack [] [] out support).2 (TerminalConsistent.empty initial terminal []) good

/-- Failure of private terminal consistency is contained in graph failure
on every reachable ideal-world execution. No probability bound for the ideal
graph failure is inferred from the separate real-world theorem. -/
theorem ideal_terminal_failure_le_graph_failure {Result : Type}
    (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result) :
    eventProb (attack.run (idealWorld RandomOracle.oracle initial terminal) ([], []))
      (fun out => ¬TerminalConsistent initial terminal out.state.1 out.state.2) ≤
    eventProb (attack.run (idealWorld RandomOracle.oracle initial terminal) ([], []))
      (fun out => ¬DataForwardFresh initial out.state.1) := by
  apply eventProb_mono_of_support
  intro out support inconsistent good
  exact inconsistent (ideal_run_from_empty initial terminal attack out support good)

end Foundation.Hash
