import Foundation.Machine.VirtualRegion
import Foundation.Machine.Subroutine

namespace Machine

namespace GuardedCompiler

/-- Fixed width of one expanded source instruction. The largest body is a
17-instruction left-boundary probe followed by the 51-instruction returning
growth routine. Unreachable padding is ordinary halt syntax. -/
def blockSize : Nat := 68

/-- Source out-of-range control targets select the final compiled halt.
This is code-layout arithmetic performed by the compiler, not an opcode. -/
def address (sourceLength pc : Nat) : Nat := blockSize * min pc sourceLength

theorem address_inRange (sourceLength pc : Nat) (h : pc ≤ sourceLength) :
    address sourceLength pc = blockSize * pc := by
  simp [address, Nat.min_eq_left h]

theorem address_outOfRange (sourceLength pc : Nat) (h : sourceLength ≤ pc) :
    address sourceLength pc = blockSize * sourceLength := by
  simp [address, Nat.min_eq_right h]

/-- Local labels are rebased; caller labels are already absolute compiled
addresses and must be retained even if numerically inside this block. In
particular a source back-edge to address zero remains a back-edge to zero. -/
def branchAt (base : Nat) (which : TapeId)
    (blankPc zeroPc onePc boundaryPc malformedPc : Nat) : Program :=
  [.branch which malformedPc (base + 1) (base + 5),
   .moveRight which, .branch which malformedPc (base + 3) (base + 9),
   .moveLeft which, .jump blankPc,
   .moveRight which, .branch which malformedPc (base + 7) (base + 11),
   .moveLeft which, .jump zeroPc,
   .moveLeft which, .jump boundaryPc,
   .moveLeft which, .jump onePc]

def leftAt (base : Nat) (which : TapeId) (readyPc boundaryPc malformedPc : Nat) : Program :=
  [.moveLeft which, .moveLeft which,
   .branch which malformedPc (base + 3) (base + 7),
   .moveRight which, .branch which malformedPc (base + 5) (base + 11),
   .moveLeft which, .jump readyPc,
   .moveRight which, .branch which malformedPc (base + 9) (base + 15),
   .moveLeft which, .jump readyPc,
   .moveLeft which, .moveRight which, .moveRight which, .jump boundaryPc,
   .moveLeft which, .jump readyPc]

@[simp] theorem branchAt_zero (which : TapeId)
    (blankPc zeroPc onePc boundaryPc malformedPc : Nat) :
    branchAt 0 which blankPc zeroPc onePc boundaryPc malformedPc =
      VirtualCell.branchCell which blankPc zeroPc onePc boundaryPc malformedPc := rfl

@[simp] theorem leftAt_zero (which : TapeId) (readyPc boundaryPc malformedPc : Nat) :
    leftAt 0 which readyPc boundaryPc malformedPc =
      VirtualCell.moveLeftCell which readyPc boundaryPc malformedPc := rfl

/-- Expand an instruction on already encoded guarded tapes. The compiler
does not supply those tapes for free: input preparation and final output
extraction remain separate machine routines. Every body contains only the
original bit-machine instructions. Tape writes, erasure and randomness use
the verified two-bit macros. Left movement tests the boundary and calls the
verified growth routine there. This definition is finite code construction;
a complete execution-simulation theorem is a separate obligation. -/
def body (sourceLength sourcePc : Nat) : Instruction → Program
  | .halt => [.halt]
  | .jump target => [.jump (address sourceLength target)]
  | .branch which blankPc zeroPc onePc =>
      branchAt (blockSize * sourcePc) which
        (address sourceLength blankPc) (address sourceLength zeroPc)
        (address sourceLength onePc) (address sourceLength sourceLength)
        (address sourceLength sourceLength)
  | .moveLeft which =>
      leftAt (blockSize * sourcePc) which (address sourceLength (sourcePc + 1))
        (blockSize * sourcePc + 17) (address sourceLength sourceLength) ++
      (VirtualCell.growLeftCell which).asSubroutine (blockSize * sourcePc + 17)
        (address sourceLength (sourcePc + 1))
  | .moveRight which =>
      (VirtualCell.moveRightCell which).asSubroutine (blockSize * sourcePc)
        (address sourceLength (sourcePc + 1))
  | .write which bit =>
      (VirtualCell.writeCell which (some bit)).asSubroutine (blockSize * sourcePc)
        (address sourceLength (sourcePc + 1))
  | .erase which =>
      (VirtualCell.writeCell which none).asSubroutine (blockSize * sourcePc)
        (address sourceLength (sourcePc + 1))
  | .randomBit which =>
      (VirtualCell.randomCell which).asSubroutine (blockSize * sourcePc)
        (address sourceLength (sourcePc + 1))

theorem body_length_le (sourceLength sourcePc : Nat) (i : Instruction) :
    (body sourceLength sourcePc i).length ≤ blockSize := by
  cases i <;> simp [body, blockSize, branchAt, leftAt, VirtualCell.growLeftCell,
    VirtualCell.moveRightCell, VirtualCell.writeCell, VirtualCell.randomCell]

def block (sourceLength sourcePc : Nat) (i : Instruction) : Program :=
  body sourceLength sourcePc i ++
    List.replicate (blockSize - (body sourceLength sourcePc i).length) .halt

theorem block_length (sourceLength sourcePc : Nat) (i : Instruction) :
    (block sourceLength sourcePc i).length = blockSize := by
  have hLength := body_length_le sourceLength sourcePc i
  simp only [block, List.length_append, List.length_replicate]
  omega

theorem block_getElem?_body (sourceLength sourcePc : Nat) (i : Instruction)
    (offset : Nat) (h : offset < (body sourceLength sourcePc i).length) :
    (block sourceLength sourcePc i)[offset]? = (body sourceLength sourcePc i)[offset]? := by
  exact List.getElem?_append_left h

def blocks (sourceLength : Nat) : Nat → Program → Program
  | _, [] => []
  | sourcePc, i :: rest => block sourceLength sourcePc i ++
      blocks sourceLength (sourcePc + 1) rest

theorem blocks_length (sourceLength sourcePc : Nat) (source : Program) :
    (blocks sourceLength sourcePc source).length = blockSize * source.length := by
  induction source generalizing sourcePc with
  | nil => simp [blocks]
  | cons i rest ih => simp [blocks, block_length, ih, Nat.mul_add, Nat.add_comm]

theorem blocks_append (sourceLength sourcePc : Nat) (front back : Program) :
    blocks sourceLength sourcePc (front ++ back) =
      blocks sourceLength sourcePc front ++
        blocks sourceLength (sourcePc + front.length) back := by
  induction front generalizing sourcePc with
  | nil => simp [blocks]
  | cons i rest ih => simp [blocks, ih, List.append_assoc, Nat.add_left_comm, Nat.add_comm]

theorem blocks_context (source : Program) (pc : Nat) (hpc : pc < source.length) :
    blocks source.length 0 source =
      blocks source.length 0 (source.take pc) ++
        block source.length pc source[pc] ++
          blocks source.length (pc + 1) (source.drop (pc + 1)) := by
  have hSplit : source = source.take pc ++ source[pc] :: source.drop (pc + 1) := by
    calc
      source = source.take pc ++ source.drop pc := (List.take_append_drop pc source).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hpc]
  calc
    blocks source.length 0 source =
        blocks source.length 0 (source.take pc ++ source[pc] :: source.drop (pc + 1)) :=
      congrArg (blocks source.length 0) hSplit
    _ = _ := by
      rw [blocks_append]
      simp [blocks, List.length_take, Nat.min_eq_left hpc.le, List.append_assoc]

theorem blocks_getElem?_block (sourceLength sourcePc : Nat) (source : Program)
    (pc offset : Nat) (hpc : pc < source.length) (hOffset : offset < blockSize) :
    (blocks sourceLength sourcePc source)[blockSize * pc + offset]? =
      (block sourceLength (sourcePc + pc) source[pc])[offset]? := by
  induction source generalizing sourcePc pc with
  | nil => simp at hpc
  | cons i rest ih =>
      cases pc with
      | zero =>
          simp only [blocks, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
          rw [List.getElem?_append_left (by simpa [block_length] using hOffset)]
          rfl
      | succ pc =>
          have hRest : pc < rest.length := by simpa using hpc
          simp only [blocks]
          rw [List.getElem?_append_right (by
            rw [block_length, Nat.mul_succ]
            omega)]
          rw [block_length]
          have hIndex : blockSize * (pc + 1) + offset - blockSize =
              blockSize * pc + offset := by
            rw [Nat.mul_succ]
            omega
          rw [hIndex]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ih (sourcePc + 1) pc hRest

/-- Executable transformation of one finite source code into one finite
expanded code, independent of security parameter and instance family. It
expects two-bit guarded representations; it does not assert whole-program
correctness or a polynomial runtime bound before simulation is proved. -/
def compile (source : Program) : Program := blocks source.length 0 source ++ [.halt]

theorem compile_length (source : Program) :
    (compile source).length = blockSize * source.length + 1 := by
  simp [compile, blocks_length]

/-- The left-growth macro is genuinely an embedded subroutine at the
compiled block's offset 17. This layout equality supports operational
invocation of its existing trace, without copying its correctness proof. -/
theorem compile_moveLeft_context (source : Program) (pc : Nat) (which : TapeId)
    (hpc : pc < source.length) (hi : source[pc] = .moveLeft which) :
    compile source = Program.withSubroutine
      (blocks source.length 0 (source.take pc) ++
        leftAt (blockSize * pc) which (address source.length (pc + 1))
          (blockSize * pc + 17) (address source.length source.length))
      (VirtualCell.growLeftCell which)
      (blocks source.length (pc + 1) (source.drop (pc + 1)) ++ [.halt])
      (address source.length (pc + 1)) := by
  have hPre : (blocks source.length 0 (source.take pc) ++
      leftAt (blockSize * pc) which (address source.length (pc + 1))
        (blockSize * pc + 17) (address source.length source.length)).length =
      blockSize * pc + 17 := by
    simp [blocks_length, leftAt, List.length_take, Nat.min_eq_left hpc.le]
  have hBody : (body source.length pc source[pc]).length = blockSize := by
    simp [hi, body, leftAt, VirtualCell.growLeftCell, blockSize]
  simp only [compile, blocks_context source pc hpc, block]
  rw [hBody]
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil, hi, body,
    Program.withSubroutine, hPre, List.append_assoc]

theorem compile_getElem?_block (source : Program) (pc offset : Nat)
    (hpc : pc < source.length) (hOffset : offset < blockSize) :
    (compile source)[blockSize * pc + offset]? =
      (block source.length pc source[pc])[offset]? := by
  have hAddress : blockSize * pc + offset < (blocks source.length 0 source).length := by
    rw [blocks_length]
    simp only [blockSize] at *
    omega
  rw [compile, List.getElem?_append_left hAddress]
  simpa using blocks_getElem?_block source.length 0 source pc offset hpc hOffset

theorem compile_getElem?_body (source : Program) (pc offset : Nat)
    (hpc : pc < source.length)
    (hOffset : offset < (body source.length pc source[pc]).length) :
    (compile source)[blockSize * pc + offset]? =
      (body source.length pc source[pc])[offset]? := by
  rw [compile_getElem?_block source pc offset hpc
    (hOffset.trans_le (body_length_le source.length pc source[pc]))]
  exact block_getElem?_body source.length pc source[pc] offset hOffset

theorem compile_getElem?_terminal (source : Program) :
    (compile source)[address source.length source.length]? = some .halt := by
  simp [compile, address, ← blocks_length source.length 0 source]

/-- A concrete compiler on finite source bitstrings. Decoding is the
existing executable program decoder, and invalid codes are rejected. -/
def compileCode (bits : List Bool) : Option (List Bool) :=
  (Program.decode bits).map (fun source => Program.encode (compile source))

theorem compileCode_encode (source : Program) :
    compileCode (Program.encode source) = some (Program.encode (compile source)) := by
  simp [compileCode]

end GuardedCompiler

end Machine
