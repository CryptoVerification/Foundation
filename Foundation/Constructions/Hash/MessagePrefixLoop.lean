import Foundation.Constructions.Hash.Chains

/-! A tail-recursive reference loop for native predecessor reconstruction.
It scans the original table order (including collisions), prepends each recovered
block, and refines `messagePrefix` without inspecting an ideal-oracle state.
The counters below count record inspections, not bit-machine transitions. -/
namespace Foundation.Hash.MessagePrefixLoop
variable {Payload Digest : Type} [DecidableEq Digest]
set_option backward.isDefEq.respectTransparency false

/-- Preserve the first-predecessor convention of `dataEdges.lookup`. -/
def find (target : Digest) : CompressionTable Payload Digest →
    Option (Digest × Payload) × Nat
  | [] => (none, 0)
  | entry :: rest =>
      if entry.1.2.1 = false ∧ entry.2 = target then
        (some (entry.1.1, entry.1.2.2), 1)
      else
        let next := find target rest
        (next.1, next.2 + 1)

theorem find_eq (target : Digest) (table : CompressionTable Payload Digest) :
    (find target table).1 = (dataEdges table).lookup target := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨⟨previous, marker, block⟩, output⟩
      have hedge : dataEdges (((previous, (marker, block)), output) :: rest) =
          if marker then dataEdges rest else (output, (previous, block)) :: dataEdges rest := by
        cases marker <;> simp [dataEdges]
      rw [find, hedge]
      cases marker with
      | true => simp [ih]
      | false =>
          by_cases he : output = target
          · subst output
            simp
          · have hb : (target == output) = false := by
              change decide (target = output) = false
              simp [Ne.symm he]
            simp [List.lookup, he, hb, ih]

theorem find_inspections_le (target : Digest) (table : CompressionTable Payload Digest) :
    (find target table).2 ≤ table.length := by
  induction table with
  | nil => simp [find]
  | cons entry rest ih =>
      simp only [find]
      split
      · simp
      · simp only [List.length_cons]
        omega

theorem find_sound (target previous : Digest) (block : Payload)
    (table : CompressionTable Payload Digest)
    (h : (find target table).1 = some (previous, block)) :
    ((previous, (false, block)), target) ∈ table := by
  rw [find_eq] at h
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp h
  apply (dataEdges_mem table previous target block).mp
  rw [he]
  simp

structure Result (Payload : Type) where
  message : Option (List Payload)
  searches : Nat
  inspections : Nat

/-- `suffix` holds recovered blocks in forward message order. Fuel is consumed
even if the selected predecessors cycle; no uniqueness premise is needed. -/
def run (initial : Digest) (table : CompressionTable Payload Digest) :
    Nat → Digest → List Payload → Result Payload
  | 0, target, suffix => ⟨if target = initial then some suffix else none, 0, 0⟩
  | fuel + 1, target, suffix =>
      if target = initial then ⟨some suffix, 0, 0⟩ else
        let found := find target table
        match found.1 with
        | none => ⟨none, 1, found.2⟩
        | some (previous, block) =>
            let next := run initial table fuel previous (block :: suffix)
            ⟨next.message, next.searches + 1, next.inspections + found.2⟩

/-- The loop refines the existing candidate on every table, not just good-event tables. -/
theorem run_eq (initial : Digest) (table : CompressionTable Payload Digest)
    (fuel : Nat) (target : Digest) (suffix : List Payload) :
    (run initial table fuel target suffix).message =
      (messagePrefix initial table fuel target).map (fun blocks => blocks ++ suffix) := by
  induction fuel generalizing target suffix with
  | zero => simp [run, messagePrefix]
  | succ fuel ih =>
      by_cases ht : target = initial
      · simp [run, messagePrefix, ht]
      · simp only [run, messagePrefix, ht, ↓reduceIte, ← find_eq]
        cases hf : (find target table).1 with
        | none => simp
        | some pair =>
            rcases pair with ⟨previous, block⟩
            simp only [ih, Option.map_map, Function.comp_def]
            congr 1
            funext blocks
            simp [List.append_assoc]

theorem run_bounds (initial : Digest) (table : CompressionTable Payload Digest)
    (fuel : Nat) (target : Digest) (suffix : List Payload) :
    (run initial table fuel target suffix).searches ≤ fuel ∧
    (run initial table fuel target suffix).inspections ≤ fuel * table.length := by
  induction fuel generalizing target suffix with
  | zero => simp [run]
  | succ fuel ih =>
      by_cases ht : target = initial
      · simp [run, ht]
      · simp only [run, ht, ↓reduceIte]
        have hc := find_inspections_le target table
        cases hf : (find target table).1 with
        | none =>
            simp only [Nat.succ_mul]
            constructor <;> omega
        | some pair =>
            rcases pair with ⟨previous, block⟩
            have hn := ih previous (block :: suffix)
            simp only [Nat.succ_mul]
            constructor <;> omega

/-- Empty-suffix entry is precisely the existing full message reconstruction. -/
theorem reconstruct_eq (initial : Digest) (table : CompressionTable Payload Digest) (target : Digest) :
    (run initial table table.length target []).message = messagePrefix initial table table.length target := by
  simpa using run_eq initial table table.length target []

theorem run_message_length (initial : Digest) (table : CompressionTable Payload Digest)
    (fuel : Nat) (target : Digest) (suffix message : List Payload)
    (h : (run initial table fuel target suffix).message = some message) :
    message.length ≤ fuel + suffix.length := by
  rw [run_eq] at h
  obtain ⟨blocks, hp, he⟩ := Option.map_eq_some_iff.mp h
  have hb := (messagePrefix_sound initial table fuel target blocks hp).2
  subst message
  simp only [List.length_append]
  omega

/-- The reference loop implements the existing terminal-message function exactly. -/
def terminal [DecidableEq Payload] (initial : Digest) (last : Payload)
    (table : CompressionTable Payload Digest) (input : CompressionInput Payload Digest) :
    Option (List Payload) :=
  if input.2.1 = true ∧ input.2.2 = last then
    (run initial table table.length input.1 []).message
  else none

theorem terminal_eq [DecidableEq Payload] (initial : Digest) (last : Payload)
    (table : CompressionTable Payload Digest) (input : CompressionInput Payload Digest) :
    terminal initial last table input = terminalMessage initial last table input := by
  simp only [terminal, terminalMessage, reconstruct_eq]

/-- A specification-level simulator using the iterative loop. This definition is
not a certificate of native execution; it supplies the refinement target for it. -/
def simulator [DecidableEq Payload] (initial : Digest) (last : Payload)
    (table : CompressionTable Payload Digest) (input : CompressionInput Payload Digest) :
    CryptoOracle.Program (SimulatorRequest Payload) Digest (CompressionTable Payload Digest × Digest) :=
  match table.lookup input with
  | some output => .done (table, output)
  | none =>
      let remember := fun output => CryptoOracle.Program.done ((input, output) :: table, output)
      match terminal initial last table input with
      | some message => .query (.inl message) remember
      | none => .query (.inr ()) remember

theorem simulator_eq [DecidableEq Payload] (initial : Digest) (last : Payload)
    (table : CompressionTable Payload Digest) (input : CompressionInput Payload Digest) :
    simulator initial last table input = simulatorProgram initial last table input := by
  simp only [simulator, simulatorProgram, terminal_eq]
  rfl

end Foundation.Hash.MessagePrefixLoop
