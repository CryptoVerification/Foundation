import Foundation.Crypto.Semantics.Oracle.NativeDeterministic
import Foundation.Crypto.Semantics.Oracle.RequestExport

/-! A balanced native bit-copy block. The source is the output tape (a
response); the destination is the caller's input/work tape. The universal
layout theorem retains arbitrary represented cells on both tapes. Every
copy takes five real transitions; no byte or whole-list primitive is added.
-/
namespace CryptoOracle.Interactive.NativeCopyBlock
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def block (base reject : Nat) : Code :=
  [.native (.branch .output reject (base + 1) (base + 3)),
   .native (.write .input false), .native (.jump (base + 5)),
   .native (.write .input true), .native (.jump (base + 5)),
   .native (.moveRight .input), .native (.moveRight .output)]

/-- Fetch obligations for embedding the block into an unchanged caller. -/
structure Located (code : Code) (base reject : Nat) : Prop where
  branch : code[base]? = some (.native (.branch .output reject (base + 1) (base + 3)))
  zeroWrite : code[base + 1]? = some (.native (.write .input false))
  zeroJoin : code[base + 2]? = some (.native (.jump (base + 5)))
  oneWrite : code[base + 3]? = some (.native (.write .input true))
  oneJoin : code[base + 4]? = some (.native (.jump (base + 5)))
  inputMove : code[base + 5]? = some (.native (.moveRight .input))
  outputMove : code[base + 6]? = some (.native (.moveRight .output))

def start (base : Nat) (destination : Tape) (left right : List (Option Bool)) (bit : Bool) :
    Machine.Configuration :=
  {pc := base, inputTape := destination, outputTape := ⟨left, some bit, right⟩}

def finish (base : Nat) (destination : Tape) (left right : List (Option Bool)) (bit : Bool) :
    Machine.Configuration :=
  {pc := base + 7, inputTape := (destination.write (some bit)).moveRight,
    outputTape := (⟨left, some bit, right⟩ : Tape).moveRight}

theorem checked (code : Code) (base reject : Nat) (located : Located code base reject)
    (destination : Tape) (left right : List (Option Bool)) (bit : Bool) :
    NativeDeterministic.run code 5 (start base destination left right bit) =
      some (finish base destination left right bit) := by
  cases bit <;>
    simp [NativeDeterministic.run, NativeDeterministic.next?, start, finish, located.branch,
      located.zeroWrite, located.zeroJoin, located.oneWrite, located.oneJoin,
      located.inputMove, located.outputMove, Machine.Instruction.next, Machine.Configuration.tape,
      Machine.Configuration.updateTape, Machine.Configuration.advance, Nat.add_assoc]

theorem timed {State : Type} (code : Code) (oracle : BitOracle State) (base reject : Nat)
    (located : Located code base reject) (destination : Tape) (left right : List (Option Bool))
    (bit : Bool) (state : State) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) 5
        (⟨state, .running (start base destination left right bit), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (finish base destination left right bit), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 5 _ _ (checked code base reject located destination left right bit)

/-- Mathematical layout specification for repeated writes and moves. This
function is never substituted for native transitions in the runtime machine. -/
def written : Tape → List Bool → Tape
  | destination, [] => destination
  | destination, bit :: rest => written ((destination.write (some bit)).moveRight) rest

def manyStart (base : Nat) (destination : Tape) (left after : List (Option Bool)) (bits : List Bool) :
    Machine.Configuration :=
  {pc := base, inputTape := destination, outputTape := RequestExport.packetTape left after bits}

def manyFinish (base : Nat) (destination : Tape) (left after : List (Option Bool)) (bits : List Bool) :
    Machine.Configuration :=
  {pc := base + 7 * bits.length, inputTape := written destination bits,
    outputTape := RequestExport.packetTape (bits.reverse.map some ++ left) after []}

theorem packet_move (left after : List (Option Bool)) (bit : Bool) (rest : List Bool) :
    (RequestExport.packetTape left after (bit :: rest)).moveRight =
      RequestExport.packetTape (some bit :: left) after rest := by
  cases rest <;> rfl

/-- Arbitrary response bits and arbitrary destination memory are handled
symbolically. The proof does not enumerate byte values or pairs of bytes. -/
theorem many_checked (code : Code) (base reject : Nat) (destination : Tape)
    (left after : List (Option Bool)) (bits : List Bool)
    (located : ∀ index, index < bits.length → Located code (base + 7 * index) reject) :
    NativeDeterministic.run code (5 * bits.length) (manyStart base destination left after bits) =
      some (manyFinish base destination left after bits) := by
  induction bits generalizing base destination left with
  | nil => simp [manyStart, manyFinish, written, NativeDeterministic.run]
  | cons bit rest ih =>
      have first : Located code base reject := by simpa using located 0 (by simp)
      have nextSites : ∀ index, index < rest.length → Located code (base + 7 + 7 * index) reject := by
        intro index inside
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          located (index + 1) (by simp only [List.length_cons]; omega)
      rw [show 5 * (bit :: rest).length = 5 + 5 * rest.length by simp; omega, NativeDeterministic.run_add]
      change (NativeDeterministic.run code 5
        (start base destination left (rest.map some ++ none :: after) bit)).bind _ = _
      rw [checked code base reject first, Option.bind_some]
      have head : finish base destination left (rest.map some ++ none :: after) bit =
          manyStart (base + 7) ((destination.write (some bit)).moveRight) (some bit :: left) after rest := by
        change ({pc := base + 7, inputTape := (destination.write (some bit)).moveRight, outputTape :=
          (RequestExport.packetTape left after (bit :: rest)).moveRight} : Machine.Configuration) = _
        rw [packet_move]
        rfl
      rw [head, ih (base + 7) ((destination.write (some bit)).moveRight) (some bit :: left) nextSites]
      congr 1
      simp [manyFinish, written, List.reverse_cons, List.map_append, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm]

theorem many_timed {State : Type} (code : Code) (oracle : BitOracle State) (base reject : Nat)
    (destination : Tape) (left after : List (Option Bool)) (bits : List Bool)
    (located : ∀ index, index < bits.length → Located code (base + 7 * index) reject)
    (state : State) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) (5 * bits.length)
      (⟨state, .running (manyStart base destination left after bits), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (manyFinish base destination left after bits), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace (5 * bits.length) _ _
    (many_checked code base reject destination left after bits located)

end CryptoOracle.Interactive.NativeCopyBlock
