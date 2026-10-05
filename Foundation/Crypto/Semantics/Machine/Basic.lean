import Foundation.Crypto.Semantics.Probability.Comp
import Mathlib.Tactic.DeriveEncodable

/-! A fixed finite-code bit machine. A transition reads or changes one tape
cell, moves one head, or changes finite control. Its program never contains an
instance family or an arbitrary Lean computation. The PMF evaluator is kept
separate from the relation of possible operational steps. -/

namespace Machine

open Foundation.Probability

/-- The two tapes have independent heads. Both contain only finite bitstrings
and blanks. The input tape is initially loaded; the output tape is blank. -/
inductive TapeId where
  | input
  | output
  deriving DecidableEq, Repr, Encodable

/-- A blank is `none`; `some false` and `some true` are bit cells. The heads
of `left` and `right` are the nearest stored cells on those sides. -/
structure Tape where
  left : List (Option Bool) := []
  current : Option Bool := none
  right : List (Option Bool) := []
  deriving DecidableEq, Repr

namespace Tape

/-- Number of represented tape cells, including the current cell. -/
def cells (t : Tape) : Nat := t.left.length + 1 + t.right.length

def ofBits : List Bool → Tape
  | [] => {}
  | b :: bs => { current := some b, right := bs.map some }

def write (t : Tape) (cell : Option Bool) : Tape :=
  { t with current := cell }

def moveLeft (t : Tape) : Tape :=
  match t.left with
  | [] => { left := [], current := none, right := t.current :: t.right }
  | cell :: rest => { left := rest, current := cell, right := t.current :: t.right }

def moveRight (t : Tape) : Tape :=
  match t.right with
  | [] => { left := t.current :: t.left, current := none, right := [] }
  | cell :: rest => { left := t.current :: t.left, current := cell, right := rest }

/-- Read the finite written portion from left to right, omitting blanks. This
is an observation of a halted tape, not a unit-cost machine instruction. -/
def bits (t : Tape) : List Bool :=
  (t.left.reverse ++ (t.current :: t.right)).filterMap id

theorem bits_length_le_cells (t : Tape) : t.bits.length ≤ t.cells := by
  have hFilter := List.length_filterMap_le id
    (t.left.reverse ++ (t.current :: t.right))
  have hLength : (t.left.reverse ++ (t.current :: t.right)).length =
      t.cells := by
    simp [cells]
    omega
  exact hFilter.trans_eq hLength

theorem cells_write (t : Tape) (cell : Option Bool) :
    (t.write cell).cells = t.cells := by
  rfl

theorem cells_moveLeft_le (t : Tape) :
    t.moveLeft.cells ≤ t.cells + 1 := by
  cases t with
  | mk left current right =>
      cases left <;> simp [moveLeft, cells] <;> omega

theorem cells_moveRight_le (t : Tape) :
    t.moveRight.cells ≤ t.cells + 1 := by
  cases t with
  | mk left current right =>
      cases right <;> simp [moveRight, cells]; omega

end Tape

/-- Every operand is a tape selector, a bit, or a fixed program address.
There is no arithmetic or whole-string operation among the instructions. -/
inductive Instruction where
  | halt
  | moveLeft (tape : TapeId)
  | moveRight (tape : TapeId)
  | write (tape : TapeId) (bit : Bool)
  | erase (tape : TapeId)
  | branch (tape : TapeId) (blankPc zeroPc onePc : Nat)
  | jump (pc : Nat)
  | randomBit (tape : TapeId)
  deriving DecidableEq, Repr, Encodable

/-- A program is a finite sequence of bit-level instructions. Its type does
not depend on any cryptographic instance family. -/
abbrev Program := List Instruction

namespace Program

/-- An explicit finite bitstring code, using a unary encoding of the
computable `Encodable` index of this finite syntax. Encoding length is not
claimed efficient and is not counted as a machine transition. -/
def encode (p : Program) : List Bool :=
  List.replicate (Encodable.encode p) true

theorem encode_injective : Function.Injective encode := by
  intro p q h
  apply Encodable.encode_injective
  have hlen := congrArg List.length h
  simpa only [encode, List.length_replicate] using hlen

/-- Partial decoder for the unary code. Invalid bitstrings and unused
`Encodable` indices are rejected. -/
def decode (bits : List Bool) : Option Program :=
  if bits = List.replicate bits.length true then
    Encodable.decode bits.length
  else none

@[simp] theorem decode_encode (p : Program) : decode (encode p) = some p := by
  simp [decode, encode]

end Program

/-- A configuration includes finite tape representations, both head
positions (inside the tape zippers), finite control, and halt status. -/
structure Configuration where
  pc : Nat := 0
  inputTape : Tape := {}
  outputTape : Tape := {}
  halted : Bool := false
  deriving DecidableEq, Repr

namespace Configuration

def initial (input : List Bool) : Configuration :=
  { inputTape := Tape.ofBits input }

def tape (c : Configuration) : TapeId → Tape
  | .input => c.inputTape
  | .output => c.outputTape

def updateTape (c : Configuration) (which : TapeId) (f : Tape → Tape) : Configuration :=
  match which with
  | .input => { c with inputTape := f c.inputTape }
  | .output => { c with outputTape := f c.outputTape }

def advance (c : Configuration) : Configuration := { c with pc := c.pc + 1 }

/-- The finite output bitstring observed on the output tape. -/
def outputBits (c : Configuration) : List Bool := c.outputTape.bits

end Configuration

/-- A non-random instruction has one successor (`inl`). A random instruction
has two possible successors (`inr`), distinguished by the sampled bit. -/
def Instruction.next (i : Instruction) (c : Configuration) :
    Configuration ⊕ (Configuration × Configuration) :=
  match i with
  | .halt => .inl { c with halted := true }
  | .moveLeft tape => .inl ((c.updateTape tape Tape.moveLeft).advance)
  | .moveRight tape => .inl ((c.updateTape tape Tape.moveRight).advance)
  | .write tape bit => .inl ((c.updateTape tape (fun t => t.write (some bit))).advance)
  | .erase tape => .inl ((c.updateTape tape (fun t => t.write none)).advance)
  | .branch tape blankPc zeroPc onePc =>
      .inl { c with pc :=
        match (c.tape tape).current with
        | none => blankPc
        | some false => zeroPc
        | some true => onePc }
  | .jump pc => .inl { c with pc := pc }
  | .randomBit tape =>
      .inr (
        (c.updateTape tape (fun t => t.write (some false))).advance,
        (c.updateTape tape (fun t => t.write (some true))).advance)

/-- A halted configuration has no operational successor. Running beyond the
end of the finite instruction list performs one transition into halt. -/
def next (p : Program) (c : Configuration) :
    Option (Configuration ⊕ (Configuration × Configuration)) :=
  if c.halted then none
  else some <| match p[c.pc]? with
    | none => .inl { c with halted := true }
    | some i => i.next c

/-- Appending an explicit halt does not change any transition: falling off
the old program already performs exactly one transition to the same halted
configuration. This gives a source-code-dependent compiler a simple,
semantically exact test case. -/
theorem next_append_halt (p : Program) (c : Configuration) :
    next (p ++ [.halt]) c = next p c := by
  by_cases hh : c.halted = true
  · simp [next, hh]
  · have hf : c.halted = false := by cases h : c.halted <;> simp_all
    simp only [next, hf, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : c.pc < p.length
    · rw [List.getElem?_append_left hlt]
    · have hle : p.length ≤ c.pc := by omega
      rw [List.getElem?_append_right hle]
      by_cases heq : c.pc = p.length
      · simp [heq, Instruction.next]
      · have hgt : p.length < c.pc := by omega
        have hne : c.pc - p.length ≠ 0 := by omega
        simp [hle, hne]

def successors (p : Program) (c : Configuration) : List Configuration :=
  match next p c with
  | none => []
  | some (.inl d) => [d]
  | some (.inr (d₀, d₁)) => [d₀, d₁]

/-- One actual machine transition. Both successors of `randomBit` are
possible; probabilities are supplied separately by `stepPMF`. -/
def Step (p : Program) (c d : Configuration) : Prop :=
  d ∈ successors p c

instance (p : Program) (c d : Configuration) : Decidable (Step p c d) :=
  inferInstanceAs (Decidable (d ∈ successors p c))

/-- An explicit halt instruction takes one actual step from a running state. -/
theorem Step.halt {p : Program} {c : Configuration}
    (hRunning : c.halted = false) (hLookup : p[c.pc]? = some .halt) :
    Step p c { c with halted := true } := by
  simp [Step, successors, next, hRunning, hLookup, Instruction.next]

theorem no_step_of_halted {p : Program} {c d : Configuration}
    (h : c.halted = true) : ¬ Step p c d := by
  simp [Step, successors, next, h]

/-- A single probabilistic transition. At a random instruction the two
successors each receive probability `1/2` via `sampleBit`. A halted state is
absorbing only for this PMF evaluator, not for the operational `Step` relation. -/
noncomputable def stepPMF (p : Program) (c : Configuration) : ProbComp Configuration :=
  match next p c with
  | none => PMF.pure c
  | some (.inl d) => PMF.pure d
  | some (.inr (d₀, d₁)) => sampleBit.map (fun b => if b then d₁ else d₀)

theorem successors_append_halt (p : Program) (c : Configuration) :
    successors (p ++ [.halt]) c = successors p c := by
  simp [successors, next_append_halt]

theorem stepPMF_append_halt (p : Program) (c : Configuration) :
    stepPMF (p ++ [.halt]) c = stepPMF p c := by
  simp [stepPMF, next_append_halt]

theorem successors_length_le_two (p : Program) (c : Configuration) :
    (successors p c).length ≤ 2 := by
  unfold successors
  split <;> simp_all

/-- Whenever the next instruction has a deterministic successor, the
operational relation has no alternative outcome. This also covers an invalid
program counter, which makes one transition into halt. -/
theorem step_unique_of_deterministic {p : Program} {c d x y : Configuration}
    (hnext : next p c = some (.inl d))
    (hx : Step p c x) (hy : Step p c y) : x = y := by
  simp only [Step, successors, hnext, List.mem_singleton] at hx hy
  exact hx.trans hy.symm

/-- One instruction can add at most one represented output-tape cell. -/
private theorem outputTape_cells_le_of_instruction
    (i : Instruction) (c d : Configuration)
    (h : d ∈ match some (i.next c) with
      | none => []
      | some (.inl target) => [target]
      | some (.inr (left, right)) => [left, right]) :
    d.outputTape.cells ≤ c.outputTape.cells + 1 := by
  cases i with
  | halt =>
      simp [Instruction.next] at h
      subst d
      simp [Tape.cells]
  | moveLeft tape =>
      simp [Instruction.next] at h
      subst d
      cases tape with
      | input => simp [Configuration.advance, Configuration.updateTape]
      | output =>
          simpa [Configuration.advance, Configuration.updateTape] using
            Tape.cells_moveLeft_le c.outputTape
  | moveRight tape =>
      simp [Instruction.next] at h
      subst d
      cases tape with
      | input => simp [Configuration.advance, Configuration.updateTape]
      | output =>
          simpa [Configuration.advance, Configuration.updateTape] using
            Tape.cells_moveRight_le c.outputTape
  | write tape bit =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [Configuration.advance, Configuration.updateTape,
        Tape.cells_write]
  | erase tape =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [Configuration.advance, Configuration.updateTape,
        Tape.cells_write]
  | branch tape blankPc zeroPc onePc =>
      simp [Instruction.next] at h
      subst d
      simp [Tape.cells]
  | jump pc =>
      simp [Instruction.next] at h
      subst d
      simp [Tape.cells]
  | randomBit tape =>
      simp [Instruction.next] at h
      rcases h with h | h <;> subst d <;>
        cases tape <;> simp [Configuration.advance, Configuration.updateTape,
          Tape.cells_write]

/-- One machine transition can add at most one represented output-tape cell.
This is the local accounting fact behind output-size bounds. -/
theorem outputTape_cells_le_of_step {p : Program} {c d : Configuration}
    (h : Step p c d) :
    d.outputTape.cells ≤ c.outputTape.cells + 1 := by
  by_cases hh : c.halted = true
  · exact False.elim (no_step_of_halted hh h)
  · have hf : c.halted = false := by cases hflag : c.halted <;> simp_all
    cases hpc : p[c.pc]? with
    | none =>
        have hd : d = { c with halted := true } := by
          simpa [Step, successors, next, hf, hpc] using h
        subst d
        simp [Tape.cells]
    | some i =>
        apply outputTape_cells_le_of_instruction i c d
        simpa [Step, successors, next, hf, hpc] using h

end Machine
