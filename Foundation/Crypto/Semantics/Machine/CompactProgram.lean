import Foundation.Crypto.Semantics.Machine.GuardedCompiler

namespace Machine

/-- A shared executable view of a finite program. The explicit instruction list
occurs only in the type and erased certificates. Length is cached, and lookup
constructs only the requested instruction. -/
structure CompactProgram (program : Program) where
  length : Nat
  length_eq : length = program.length
  lookup : Nat → Option Instruction
  lookup_eq : ∀ pc, lookup pc = program[pc]?

namespace CompactProgram

@[macro_inline] def literal (program : Program) : CompactProgram program where
  length := program.length
  length_eq := rfl
  lookup := fun pc => program[pc]?
  lookup_eq := fun _ => rfl

@[macro_inline] def cons {i : Instruction} {program : Program}
    (instruction : Instruction) (correct : instruction = i)
    (rest : CompactProgram program) : CompactProgram (i :: program) where
  length := rest.length + 1
  length_eq := by simp [rest.length_eq]
  lookup := fun pc => match pc with
    | 0 => some instruction
    | n + 1 => rest.lookup n
  lookup_eq := by intro pc; cases pc <;> simp [correct, rest.lookup_eq]

@[macro_inline] def append {p q : Program} (first : CompactProgram p)
    (second : CompactProgram q) : CompactProgram (p ++ q) where
  length := first.length + second.length
  length_eq := by simp [first.length_eq, second.length_eq]
  lookup := fun pc => if pc < first.length then first.lookup pc
    else second.lookup (pc - first.length)
  lookup_eq := by
    intro pc
    by_cases h : pc < first.length
    · simp only [if_pos h, first.lookup_eq]
      exact (List.getElem?_append_left (by simpa [first.length_eq] using h)).symm
    · simp only [if_neg h, second.lookup_eq]
      rw [List.getElem?_append_right (by simpa [first.length_eq] using Nat.le_of_not_gt h)]
      rw [first.length_eq]

@[macro_inline] def subroutine {p : Program} (source : CompactProgram p)
    {base returnPc : Nat} (baseValue returnValue : Nat)
    (base_eq : baseValue = base) (return_eq : returnValue = returnPc) :
    CompactProgram (p.asSubroutine base returnPc) where
  length := source.length + 1
  length_eq := by simp [source.length_eq]
  lookup := fun pc => if pc < source.length then
      (source.lookup pc).map (Instruction.asSubroutine baseValue returnValue source.length)
    else if pc = source.length then some (.jump returnValue) else none
  lookup_eq := by
    intro pc
    by_cases h : pc < source.length
    · have hp : pc < p.length := by simpa [source.length_eq] using h
      simp only [source.lookup_eq, base_eq, return_eq, source.length_eq, if_pos hp]
      exact (p.asSubroutine_getElem?_source base returnPc pc hp).symm
    · simp only [if_neg h]
      by_cases e : pc = source.length
      · simp only [if_pos e, return_eq]
        rw [e, source.length_eq, Program.asSubroutine_getElem?_return]
      · simp only [if_neg e]
        symm
        apply List.getElem?_eq_none
        simp only [Program.asSubroutine_length, ← source.length_eq]
        omega

@[macro_inline] def guarded {p : Program} (source : CompactProgram p) :
    CompactProgram (GuardedCompiler.compile p) where
  length := 68 * source.length + 1
  length_eq := by simp [GuardedCompiler.compile_length, GuardedCompiler.blockSize, source.length_eq]
  lookup := fun pc => if pc < 68 * source.length then
      (source.lookup (pc / 68)).bind fun i =>
        (GuardedCompiler.block source.length (pc / 68) i)[pc % 68]?
    else if pc = 68 * source.length then some .halt else none
  lookup_eq := by
    intro pc
    by_cases h : pc < 68 * source.length
    · have hi : pc / 68 < p.length := by rw [← source.length_eq]; omega
      have hm : pc % 68 < GuardedCompiler.blockSize := by
        unfold GuardedCompiler.blockSize; omega
      have h' : pc < 68 * p.length := by simpa [source.length_eq] using h
      simp only [source.lookup_eq, List.getElem?_eq_getElem hi,
        Option.bind_some, source.length_eq, if_pos h']
      unfold GuardedCompiler.compile
      rw [List.getElem?_append_left (by
        rw [GuardedCompiler.blocks_length, GuardedCompiler.blockSize, ← source.length_eq]
        exact h)]
      have hp : 68 * (pc / 68) + pc % 68 = pc := by omega
      have hb := GuardedCompiler.blocks_getElem?_block p.length 0 p
        (pc / 68) (pc % 68) hi hm
      rw [GuardedCompiler.blockSize, hp] at hb
      simpa using hb.symm
    · simp only [if_neg h]
      by_cases e : pc = 68 * source.length
      · simp only [if_pos e]
        unfold GuardedCompiler.compile
        rw [List.getElem?_append_right (by
          rw [GuardedCompiler.blocks_length, GuardedCompiler.blockSize, ← source.length_eq]
          omega)]
        simp [GuardedCompiler.blocks_length, GuardedCompiler.blockSize, ← source.length_eq, e]
      · simp only [if_neg e]
        symm
        apply List.getElem?_eq_none
        rw [GuardedCompiler.compile_length, GuardedCompiler.blockSize, ← source.length_eq]
        omega

end CompactProgram
end Machine

namespace Machine.CompactProgram

@[macro_inline] def replicate {count : Nat} {i : Instruction}
    (countValue : Nat) (count_eq : countValue = count)
    (instruction : Instruction) (correct : instruction = i) :
    CompactProgram (List.replicate count i) where
  length := countValue
  length_eq := by simp [count_eq]
  lookup := fun pc => if pc < countValue then some instruction else none
  lookup_eq := by intro pc; simp [List.getElem?_replicate, count_eq, correct]

@[macro_inline] def map {p : Program} (source : CompactProgram p)
    {f : Instruction → Instruction} (function : Instruction → Instruction)
    (correct : function = f) : CompactProgram (p.map f) where
  length := source.length
  length_eq := by simp [source.length_eq]
  lookup := fun pc => (source.lookup pc).map function
  lookup_eq := by intro pc; simp [source.lookup_eq, correct]

/-- Fetch a single instruction through the shared view. This is exactly the
original transition, including fall-off halt and both random successors. -/
@[macro_inline] def next {p : Program} (source : CompactProgram p) (c : Configuration) :
    Option (Configuration ⊕ (Configuration × Configuration)) :=
  if c.halted then none
  else some <| match source.lookup c.pc with
    | none => .inl { c with halted := true }
    | some i => i.next c

theorem next_eq {p : Program} (source : CompactProgram p) (c : Configuration) :
    source.next c = Machine.next p c := by
  simp only [next, Machine.next, source.lookup_eq]
  rfl

end Machine.CompactProgram

namespace Machine.CompactProgram

/-- Change only the specification along a proved equality, retaining the shared data. -/
@[macro_inline] def reindex {p q : Program} (source : CompactProgram p)
    (correct : p = q) : CompactProgram q where
  length := source.length
  length_eq := by rw [← correct]; exact source.length_eq
  lookup := source.lookup
  lookup_eq := by intro pc; rw [← correct]; exact source.lookup_eq pc

end Machine.CompactProgram
