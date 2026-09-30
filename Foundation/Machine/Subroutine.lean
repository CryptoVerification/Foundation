import Foundation.Machine.Basic

namespace Machine

/-- Rebase an absolute source address when embedding a finite program at
`base`. A jump beyond the source program is a fall-off halt in the source
machine, so the embedded code redirects it to `returnPc`. -/
def subroutineAddress (base returnPc sourceLength pc : Nat) : Nat :=
  if pc < sourceLength then base + pc else returnPc

@[simp] theorem subroutineAddress_inRange (base returnPc sourceLength pc : Nat)
    (h : pc < sourceLength) :
    subroutineAddress base returnPc sourceLength pc = base + pc := by
  simp [subroutineAddress, h]

@[simp] theorem subroutineAddress_outOfRange (base returnPc sourceLength pc : Nat)
    (h : sourceLength ≤ pc) :
    subroutineAddress base returnPc sourceLength pc = returnPc := by
  simp [subroutineAddress, Nat.not_lt.mpr h]

/-- Rewrite one source instruction for a subroutine. `halt` returns, while
explicit control-flow addresses are rebased or redirected on fall-off. Tape
operations and fresh random-bit steps are unchanged. -/
def Instruction.asSubroutine (base returnPc sourceLength : Nat) :
    Instruction → Instruction
  | .halt => .jump returnPc
  | .jump pc => .jump (subroutineAddress base returnPc sourceLength pc)
  | .branch tape blankPc zeroPc onePc =>
      .branch tape
        (subroutineAddress base returnPc sourceLength blankPc)
        (subroutineAddress base returnPc sourceLength zeroPc)
        (subroutineAddress base returnPc sourceLength onePc)
  | .moveLeft tape => .moveLeft tape
  | .moveRight tape => .moveRight tape
  | .write tape bit => .write tape bit
  | .erase tape => .erase tape
  | .randomBit tape => .randomBit tape

/-- A finite source program embedded at `base`, with a final jump for
fall-through termination. The surrounding program must place this block at
exactly `base` and provide code at `returnPc`; those layout obligations are
separate from the syntactic transformation. -/
def Program.asSubroutine (source : Program) (base returnPc : Nat) : Program :=
  source.map (Instruction.asSubroutine base returnPc source.length) ++
    [.jump returnPc]

@[simp] theorem Program.asSubroutine_length
    (source : Program) (base returnPc : Nat) :
    (source.asSubroutine base returnPc).length = source.length + 1 := by
  simp [Program.asSubroutine]

/-- Every instruction inside the embedded source block is the corresponding
rewritten source instruction. -/
theorem Program.asSubroutine_getElem?_source
    (source : Program) (base returnPc i : Nat)
    (hi : i < source.length) :
    (source.asSubroutine base returnPc)[i]? =
      (source[i]?).map
        (Instruction.asSubroutine base returnPc source.length) := by
  unfold Program.asSubroutine
  rw [List.getElem?_append_left (by simpa using hi)]
  simp

/-- Falling through the embedded source reaches its explicit return jump. -/
theorem Program.asSubroutine_getElem?_return
    (source : Program) (base returnPc : Nat) :
    (source.asSubroutine base returnPc)[source.length]? =
      some (.jump returnPc) := by
  simp [Program.asSubroutine]

/-- Place the transformed code after a finite prefix. The prefix length is
the absolute starting address used by `asSubroutine`. -/
def Program.withSubroutine (pre source suffix : Program)
    (returnPc : Nat) : Program :=
  pre ++ source.asSubroutine pre.length returnPc ++ suffix

/-- Prefix instructions keep their original absolute addresses. -/
theorem Program.withSubroutine_getElem?_pre
    (pre source suffix : Program) (returnPc pc : Nat)
    (hpc : pc < pre.length) :
    (withSubroutine pre source suffix returnPc)[pc]? = pre[pc]? := by
  simp [withSubroutine, List.getElem?_append_left hpc]

/-- A rebased source address reads exactly the rewritten instruction in a
wrapper with an arbitrary prefix and suffix. -/
theorem Program.withSubroutine_getElem?_source
    (pre source suffix : Program) (returnPc pc : Nat)
    (hpc : pc < source.length) :
    (withSubroutine pre source suffix returnPc)[pre.length + pc]? =
      (source[pc]?).map
        (Instruction.asSubroutine pre.length returnPc source.length) := by
  unfold withSubroutine
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by omega)]
  simpa using source.asSubroutine_getElem?_source pre.length returnPc pc hpc

/-- The instruction immediately after the source block is its return jump,
including when the source program is empty. -/
theorem Program.withSubroutine_getElem?_return
    (pre source suffix : Program) (returnPc : Nat) :
    (withSubroutine pre source suffix returnPc)[pre.length + source.length]? =
      some (.jump returnPc) := by
  unfold withSubroutine
  rw [List.getElem?_append_left (by simp)]
  rw [List.getElem?_append_right (by omega)]
  simpa using source.asSubroutine_getElem?_return pre.length returnPc

/-- Suffix addresses start after the source block and its explicit return
jump. -/
theorem Program.withSubroutine_getElem?_suffix
    (pre source suffix : Program) (returnPc pc : Nat) :
    (withSubroutine pre source suffix returnPc)[pre.length + source.length + 1 + pc]? =
      suffix[pc]? := by
  unfold withSubroutine
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, Program.asSubroutine_length]
  congr 1
  omega

/-- At an address inside the copied block, the operational machine executes
the rewritten instruction. This is a local step statement; equivalence with
a complete source execution still needs a simulation invariant. -/
theorem Program.next_withSubroutine_source
    (pre source suffix : Program) (returnPc pc : Nat)
    (c : Configuration) (hpc : pc < source.length)
    (haddr : c.pc = pre.length + pc) (hactive : c.halted = false) :
    next (withSubroutine pre source suffix returnPc) c =
      some ((Instruction.asSubroutine pre.length returnPc source.length
        source[pc]).next c) := by
  simp [next, hactive, haddr,
    Program.withSubroutine_getElem?_source pre source suffix returnPc pc hpc,
    List.getElem?_eq_getElem hpc]

/-- A fall-through at the end of the embedded block transfers control to the
specified continuation in one machine step. -/
theorem Program.next_withSubroutine_return
    (pre source suffix : Program) (returnPc : Nat)
    (c : Configuration)
    (haddr : c.pc = pre.length + source.length)
    (hactive : c.halted = false) :
    next (withSubroutine pre source suffix returnPc) c =
      some (.inl { c with pc := returnPc }) := by
  simp [next, hactive, haddr,
    Program.withSubroutine_getElem?_return pre source suffix returnPc,
    Instruction.next]

/-- Two invocations of the same source code. The first returns to `middle`;
the second returns to `post`. These blocks alone do not prepare the tapes or
establish the semantic correctness of a protocol wrapper. -/
def Program.withTwoSubroutines (pre middle post source : Program) : Program :=
  let firstBase := pre.length
  let middleBase := firstBase + source.length + 1
  let secondBase := middleBase + middle.length
  let postBase := secondBase + source.length + 1
  pre ++ source.asSubroutine firstBase middleBase ++ middle ++
    source.asSubroutine secondBase postBase ++ post

@[simp] theorem Program.withTwoSubroutines_length
    (pre middle post source : Program) :
    (withTwoSubroutines pre middle post source).length =
      pre.length + 2 * (source.length + 1) + middle.length + post.length := by
  simp [withTwoSubroutines]
  omega

/-- View the first copied block as a single subroutine inside a larger
wrapper. -/
theorem Program.withTwoSubroutines_first_layout
    (pre middle post source : Program) :
    withTwoSubroutines pre middle post source =
      withSubroutine pre source
        (middle ++ source.asSubroutine
          (pre.length + source.length + 1 + middle.length)
          (pre.length + source.length + 1 + middle.length +
            source.length + 1) ++ post)
        (pre.length + source.length + 1) := by
  simp [withTwoSubroutines, withSubroutine, List.append_assoc, Nat.add_assoc]

/-- View the second copied block as a subroutine after the complete first
block and the intervening code. -/
theorem Program.withTwoSubroutines_second_layout
    (pre middle post source : Program) :
    withTwoSubroutines pre middle post source =
      withSubroutine
        (pre ++ source.asSubroutine pre.length
          (pre.length + source.length + 1) ++ middle)
        source post
        (pre.length + source.length + 1 + middle.length +
          source.length + 1) := by
  simp [withTwoSubroutines, withSubroutine, List.append_assoc, Nat.add_assoc]

/-- The first invocation reads the first rebased copy of the source. -/
theorem Program.withTwoSubroutines_getElem?_first
    (pre middle post source : Program) (pc : Nat)
    (hpc : pc < source.length) :
    (withTwoSubroutines pre middle post source)[pre.length + pc]? =
      (source[pc]?).map (Instruction.asSubroutine pre.length
        (pre.length + source.length + 1) source.length) := by
  rw [withTwoSubroutines_first_layout]
  exact withSubroutine_getElem?_source pre source _ _ pc hpc

/-- The second invocation reads the same source at a different absolute
address and returns to the code after both copies. -/
theorem Program.withTwoSubroutines_getElem?_second
    (pre middle post source : Program) (pc : Nat)
    (hpc : pc < source.length) :
    (withTwoSubroutines pre middle post source)[pre.length + source.length + 1 + middle.length + pc]? =
      (source[pc]?).map (Instruction.asSubroutine
        (pre.length + source.length + 1 + middle.length)
        (pre.length + source.length + 1 + middle.length +
          source.length + 1) source.length) := by
  rw [withTwoSubroutines_second_layout]
  simpa only [List.length_append, asSubroutine_length, Nat.add_assoc]
    using withSubroutine_getElem?_source
      (pre ++ source.asSubroutine pre.length
        (pre.length + source.length + 1) ++ middle)
      source post
      (pre.length + source.length + 1 + middle.length +
        source.length + 1) pc hpc

/-- Falling off the first copy transfers control to the intervening code. -/
theorem Program.withTwoSubroutines_getElem?_firstReturn
    (pre middle post source : Program) :
    (withTwoSubroutines pre middle post source)[pre.length + source.length]? =
      some (.jump (pre.length + source.length + 1)) := by
  rw [withTwoSubroutines_first_layout]
  exact withSubroutine_getElem?_return pre source _ _

/-- Falling off the second copy transfers control to the final code. -/
theorem Program.withTwoSubroutines_getElem?_secondReturn
    (pre middle post source : Program) :
    (withTwoSubroutines pre middle post source)[pre.length + source.length + 1 + middle.length + source.length]? =
      some (.jump (pre.length + source.length + 1 + middle.length +
        source.length + 1)) := by
  rw [withTwoSubroutines_second_layout]
  simpa only [List.length_append, asSubroutine_length, Nat.add_assoc]
    using withSubroutine_getElem?_return
      (pre ++ source.asSubroutine pre.length
        (pre.length + source.length + 1) ++ middle)
      source post
      (pre.length + source.length + 1 + middle.length +
        source.length + 1)

@[simp] theorem Program.asSubroutine_nil (base returnPc : Nat) :
    (asSubroutine [] base returnPc) = [.jump returnPc] := rfl

@[simp] theorem Program.asSubroutine_halt (base returnPc : Nat) :
    (asSubroutine [.halt] base returnPc) =
      [.jump returnPc, .jump returnPc] := rfl

/-- The subroutine transformer operates on finite program codes without
choice or family-dependent program selection. This does not yet prove that
a surrounding wrapper executes the subroutine correctly. -/
def subroutineCode (base returnPc : Nat) (bits : List Bool) :
    Option (List Bool) :=
  (Program.decode bits).map fun source =>
    Program.encode (source.asSubroutine base returnPc)

@[simp] theorem subroutineCode_encode (base returnPc : Nat)
    (source : Program) :
    subroutineCode base returnPc (Program.encode source) =
      some (Program.encode (source.asSubroutine base returnPc)) := by
  simp [subroutineCode]

end Machine
