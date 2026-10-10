import Foundation.Constructions.Hash.PrefixFree
import Foundation.Crypto.Semantics.Oracle.CallExecution
import Foundation.Crypto.Semantics.Oracle.StraightLine
import Foundation.Crypto.Semantics.VectorEncoding

/-! Native preparation of a compression packet. The digest is retained on the
actual response tape, a marked payload is appended one bit at a time, and the
head is rewound before issuing the next call. The caller supplies fixed-width
bit representations; no whole-string native instruction is introduced. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open StraightLine
set_option backward.isDefEq.respectTransparency false

/-- Every bit costs a write and a one-cell move. -/
def writeActions (bits : List Bool) : List Action :=
  bits.flatMap (fun bit => [.write .output (some bit), .right .output])

def rightActions (count : Nat) : List Action := List.replicate count (.right .output)
def leftActions (count : Nat) : List Action := List.replicate count (.left .output)

@[simp] theorem writeActions_length (bits : List Bool) :
    (writeActions bits).length = 2 * bits.length := by
  induction bits <;> simp_all [writeActions]; omega

@[simp] theorem rightActions_length (count : Nat) : (rightActions count).length = count := by
  simp [rightActions]
@[simp] theorem leftActions_length (count : Nat) : (leftActions count).length = count := by
  simp [leftActions]

theorem write_execute (pc : Nat) (input : Tape) (before bits : List Bool) :
    execute (writeActions bits)
      { pc := pc, inputTape := input, outputTape := { left := before.reverse.map some } } =
    ({ pc := pc + 2 * bits.length, inputTape := input, outputTape := { left := (before ++ bits).reverse.map some } } : Machine.Configuration) := by
  induction bits generalizing pc before with
  | nil => simp [writeActions, execute]
  | cons bit bits ih =>
      simpa [writeActions, execute, apply, Machine.Configuration.updateTape,
        Machine.Configuration.advance, Tape.write, Tape.moveRight,
        List.reverse_append, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.mul_add, Nat.add_comm, Nat.add_left_comm] using
        ih (pc + 2) (before ++ [bit])

theorem right_execute (pc : Nat) (input : Tape) (bits : List Bool)
    (left : List (Option Bool)) :
    execute (rightActions bits.length)
      { pc := pc, inputTape := input, outputTape := { ResponseLoading.loaded bits with left := left } } =
    ({ pc := pc + bits.length, inputTape := input, outputTape := { left := bits.reverse.map some ++ left } } : Machine.Configuration) := by
  induction bits generalizing pc left with
  | nil => simp [rightActions, execute, ResponseLoading.loaded, ResponseLoading.fromCells]
  | cons bit bits ih =>
      have h := ih (pc + 1) (some bit :: left)
      cases bits with
      | nil => simp [rightActions, execute, apply, Machine.Configuration.updateTape,
          Machine.Configuration.advance, ResponseLoading.loaded, ResponseLoading.fromCells, Tape.moveRight]
      | cons head rest => simpa [rightActions, List.replicate_succ, execute, apply,
        Machine.Configuration.updateTape, Machine.Configuration.advance,
        ResponseLoading.loaded, ResponseLoading.fromCells, Tape.moveRight,
        List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem left_execute (pc : Nat) (input : Tape) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    execute (leftActions left.length)
      { pc := pc, inputTape := input, outputTape := ⟨left.map some, current, right⟩ } =
    ({ pc := pc + left.length, inputTape := input, outputTape := ResponseLoading.fromCells (left.reverse.map some ++ current :: right) } : Machine.Configuration) := by
  induction left generalizing pc current right with
  | nil => simp [leftActions, execute, ResponseLoading.fromCells]
  | cons bit left ih =>
      simpa [leftActions, List.replicate_succ, execute, apply, Machine.Configuration.updateTape,
        Machine.Configuration.advance, Tape.moveLeft, List.reverse_cons,
        List.map_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (pc + 1) (some bit) (current :: right)

/-- Extend an n-bit digest by a marked payload and position its head for the
call controller. The length parameter is the real retained digest length. -/
def prepareActions (digestWidth : Nat) (markedPayload : List Bool) : List Action :=
  rightActions digestWidth ++ writeActions markedPayload ++
    leftActions (digestWidth + markedPayload.length)

@[simp] theorem prepareActions_length (digestWidth : Nat) (markedPayload : List Bool) :
    (prepareActions digestWidth markedPayload).length = 2 * digestWidth + 3 * markedPayload.length := by
  simp [prepareActions]
  omega

theorem prepare_execute (pc : Nat) (input : Tape) (digest markedPayload : List Bool) :
    execute (prepareActions digest.length markedPayload)
      { pc := pc, inputTape := input, outputTape := ResponseLoading.loaded digest } =
    ({ pc := pc + (2 * digest.length + 3 * markedPayload.length), inputTape := input, outputTape := ResponseLoading.loaded (digest ++ markedPayload) } : Machine.Configuration) := by
  rw [prepareActions, execute_append, execute_append]
  have h := right_execute pc input digest []
  have empty_left : ({ ResponseLoading.loaded digest with left := [] } : Tape) =
      ResponseLoading.loaded digest := rfl
  rw [empty_left] at h
  rw [h]
  simp only [List.append_nil]
  rw [write_execute]
  rw [show digest.length + markedPayload.length = (digest ++ markedPayload).reverse.length by simp; omega,
    left_execute]
  simp only [ResponseLoading.loaded, List.length_reverse, List.length_append, List.reverse_reverse]
  congr 1; omega

/-- The finite emitted preparation code runs in an arbitrary surrounding
program and preserves its input tape and the private oracle state/history. -/
theorem prepare_run {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (before after : Code)
    (input : Tape) (digest markedPayload : List Bool) :
    TimedExecution.eval
      (Reification.timedStep
        (before ++ StraightLine.code (prepareActions digest.length markedPayload) ++ after) oracle)
      (2 * digest.length + 3 * markedPayload.length)
      (⟨state, .running { pc := before.length, inputTape := input, outputTape := ResponseLoading.loaded digest }, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running { pc := before.length + (2 * digest.length + 3 * markedPayload.length), inputTape := input, outputTape := ResponseLoading.loaded (digest ++ markedPayload) }, trace⟩ := by
  have h := StraightLine.public_run oracle state trace before after
    (prepareActions digest.length markedPayload)
    { pc := before.length, inputTape := input, outputTape := ResponseLoading.loaded digest } rfl rfl
  rw [prepareActions_length, prepare_execute] at h
  exact h

/-- A real compression-call fragment. Its finite instruction list appends the
marked payload to the retained digest, rewinds, transfers, calls once, and
loads the next digest. All local transfer transitions are included. -/
def compressionCode (digestWidth : Nat) (markedPayload : List Bool) : Code :=
  StraightLine.code (prepareActions digestWidth markedPayload) ++ [.call]

@[simp] theorem compressionCode_length (digestWidth : Nat) (markedPayload : List Bool) :
    (compressionCode digestWidth markedPayload).length =
      2 * digestWidth + 3 * markedPayload.length + 1 := by
  simp [compressionCode, StraightLine.code]

/-- No computation inside `oracle` is included in the displayed duration.
The private state and complete transcript in the conclusion are exact. -/
theorem compression_run {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (before after : Code)
    (input : Tape) (digest markedPayload : List Bool)
    (width : ∀ answer ∈ (oracle state (digest ++ markedPayload)).support,
      answer.2.length = digest.length) :
    TimedExecution.eval
      (Reification.timedStep (before ++ compressionCode digest.length markedPayload ++ after) oracle)
      (7 * digest.length + 5 * markedPayload.length + 6)
      (⟨state, .running { pc := before.length, inputTape := input, outputTape := ResponseLoading.loaded digest }, trace⟩ : Configuration State) =
    (oracle state (digest ++ markedPayload)).map (fun answer =>
      (⟨answer.1, .running {
        pc := before.length + (2 * digest.length + 3 * markedPayload.length) + 1, inputTape := input, outputTape := ResponseLoading.loaded answer.2 },
        (digest ++ markedPayload, answer.2) :: trace⟩ : Configuration State)) := by
  rw [show 7 * digest.length + 5 * markedPayload.length + 6 =
      (2 * digest.length + 3 * markedPayload.length) +
        (2 * (digest ++ markedPayload).length + 3 * digest.length + 6) by simp; omega,
    TimedExecution.eval_add]
  have prep := prepare_run oracle state trace before (.call :: after) input digest markedPayload
  simp only [compressionCode, List.append_assoc, List.singleton_append] at prep ⊢
  rw [prep, PMF.pure_bind]
  exact CallExecution.run _ oracle _ state trace (digest ++ markedPayload) digest.length rfl
    (by simp [StraightLine.code, prepareActions_length]) rfl width

end Foundation.Hash.Native
