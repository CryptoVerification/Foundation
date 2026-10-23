import Foundation.Crypto.Semantics.Oracle.NativeDeterministicHalt
import Foundation.Crypto.Semantics.Oracle.NativeCopyBlock

/-! Symbolic native comparison of equal-width bitstrings. Matching bits cost
four transitions; the first mismatch branches to a genuine rejecting halt.
The checked result retains both physical tapes and the actual stopping time.
There is no enumeration of byte values and no whole-string runtime primitive.
-/
namespace CryptoOracle.Interactive.NativeCompareBlock
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

structure Located (code : Code) (base reject : Nat) : Prop where
  inputBranch : code[base]? = some (.native (.branch .input reject (base + 1) (base + 2)))
  zeroBranch : code[base + 1]? = some (.native (.branch .output reject (base + 3) reject))
  oneBranch : code[base + 2]? = some (.native (.branch .output reject reject (base + 3)))
  inputMove : code[base + 3]? = some (.native (.moveRight .input))
  outputMove : code[base + 4]? = some (.native (.moveRight .output))

structure HaltAt (code : Code) (base : Nat) (verdict : Bool) : Prop where
  write : code[base]? = some (.native (.write .output verdict))
  halt : code[base + 1]? = some (.native .halt)

def frame (base : Nat) (inputLeft outputLeft inputAfter outputAfter : List (Option Bool))
    (pairs : List (Bool × Bool)) : Machine.Configuration :=
  {pc := base,
   inputTape := RequestExport.packetTape inputLeft inputAfter (pairs.map Prod.fst),
   outputTape := RequestExport.packetTape outputLeft outputAfter (pairs.map Prod.snd)}

def stopped (base : Nat) (verdict : Bool) (machine : Machine.Configuration) : Machine.Configuration :=
  {machine with pc := base + 1, outputTape := machine.outputTape.write (some verdict), halted := true}

def result (base reject : Nat) (inputLeft outputLeft inputAfter outputAfter : List (Option Bool)) :
    List (Bool × Bool) → Machine.Configuration × Nat
  | [] => (stopped base true (frame base inputLeft outputLeft inputAfter outputAfter []), 2)
  | (first, second) :: rest =>
      if first = second then
        let tail := result (base + 5) reject (some first :: inputLeft) (some second :: outputLeft)
          inputAfter outputAfter rest
        (tail.1, 4 + tail.2)
      else (stopped reject false (frame base inputLeft outputLeft inputAfter outputAfter ((first, second) :: rest)), 4)

theorem halt_checked (code : Code) (base : Nat) (verdict : Bool) (located : HaltAt code base verdict)
    (machine : Machine.Configuration) (active : machine.halted = false) :
    NativeDeterministic.run code 2 {machine with pc := base} = some (stopped base verdict machine) := by
  simp [NativeDeterministic.run, NativeDeterministic.next?, stopped, located.write, located.halt,
    Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance, active]

theorem match_checked (code : Code) (base reject : Nat) (located : Located code base reject)
    (inputLeft outputLeft inputAfter outputAfter : List (Option Bool)) (bit : Bool)
    (rest : List (Bool × Bool)) :
    NativeDeterministic.run code 4 (frame base inputLeft outputLeft inputAfter outputAfter ((bit, bit) :: rest)) =
      some (frame (base + 5) (some bit :: inputLeft) (some bit :: outputLeft) inputAfter outputAfter rest) := by
  have moves :
      ({ pc := base + 5,
         inputTape := (RequestExport.packetTape inputLeft inputAfter (bit :: rest.map Prod.fst)).moveRight,
         outputTape := (RequestExport.packetTape outputLeft outputAfter (bit :: rest.map Prod.snd)).moveRight } :
        Machine.Configuration) =
      frame (base + 5) (some bit :: inputLeft) (some bit :: outputLeft) inputAfter outputAfter rest := by
    rw [NativeCopyBlock.packet_move, NativeCopyBlock.packet_move]
    rfl
  rw [← moves]
  cases bit <;>
    simp [NativeDeterministic.run, NativeDeterministic.next?, frame, RequestExport.packetTape,
      located.inputBranch, located.zeroBranch, located.oneBranch, located.inputMove, located.outputMove,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance]

theorem mismatch_checked (code : Code) (base reject : Nat) (located : Located code base reject)
    (inputLeft outputLeft inputAfter outputAfter : List (Option Bool)) (first second : Bool)
    (different : first ≠ second) (rest : List (Bool × Bool)) :
    NativeDeterministic.run code 2 (frame base inputLeft outputLeft inputAfter outputAfter ((first, second) :: rest)) =
      some {frame base inputLeft outputLeft inputAfter outputAfter ((first, second) :: rest) with pc := reject} := by
  cases first <;> cases second <;>
    simp_all [NativeDeterministic.run, NativeDeterministic.next?, frame, RequestExport.packetTape,
      located.inputBranch, located.zeroBranch, located.oneBranch,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance]

theorem checked (code : Code) (base reject : Nat)
    (inputLeft outputLeft inputAfter outputAfter : List (Option Bool)) (pairs : List (Bool × Bool))
    (located : ∀ index, index < pairs.length → Located code (base + 5 * index) reject)
    (accept : HaltAt code (base + 5 * pairs.length) true) (rejecting : HaltAt code reject false) :
    NativeDeterministic.finish code (4 * pairs.length + 2)
      (frame base inputLeft outputLeft inputAfter outputAfter pairs) =
      some (result base reject inputLeft outputLeft inputAfter outputAfter pairs) := by
  induction pairs generalizing base inputLeft outputLeft with
  | nil =>
      have accepts : HaltAt code base true := by simpa using accept
      have run := halt_checked code base true accepts
        (frame base inputLeft outputLeft inputAfter outputAfter []) rfl
      change NativeDeterministic.run code 2 (frame base inputLeft outputLeft inputAfter outputAfter []) =
        some (stopped base true (frame base inputLeft outputLeft inputAfter outputAfter [])) at run
      change NativeDeterministic.finish code (2 + 0) _ = _
      rw [NativeDeterministic.finish_after_run code 2 0 _ _ run]
      simp [NativeDeterministic.finish, result, stopped]
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      have firstSite : Located code base reject := by simpa using located 0 (by simp)
      have fuel : 4 * ((first, second) :: rest).length + 2 = 4 + (4 * rest.length + 2) := by simp; omega
      by_cases same : first = second
      · subst second
        have tailSites : ∀ index, index < rest.length → Located code (base + 5 + 5 * index) reject := by
          intro index inside
          simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            located (index + 1) (by simp only [List.length_cons]; omega)
        have tailAccept : HaltAt code (base + 5 + 5 * rest.length) true := by
          simpa [List.length_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using accept
        rw [fuel, NativeDeterministic.finish_after_run code 4 (4 * rest.length + 2) _ _
          (match_checked code base reject firstSite inputLeft outputLeft inputAfter outputAfter first rest)]
        rw [ih (base + 5) (some first :: inputLeft) (some first :: outputLeft) tailSites tailAccept]
        simp [result]
      · have rejected := (mismatch_checked code base reject firstSite inputLeft outputLeft inputAfter outputAfter
          first second same rest)
        have halt := halt_checked code reject false rejecting
          (frame base inputLeft outputLeft inputAfter outputAfter ((first, second) :: rest)) rfl
        have run : NativeDeterministic.run code 4
            (frame base inputLeft outputLeft inputAfter outputAfter ((first, second) :: rest)) =
            some (stopped reject false (frame base inputLeft outputLeft inputAfter outputAfter ((first, second) :: rest))) := by
          rw [show 4 = 2 + 2 by rfl, NativeDeterministic.run_add, rejected, Option.bind_some, halt]
        rw [fuel, NativeDeterministic.finish_after_run code 4 (4 * rest.length + 2) _ _ run]
        simp [NativeDeterministic.finish, result, same, stopped]

theorem decision (base reject : Nat) (inputLeft outputLeft inputAfter outputAfter : List (Option Bool))
    (pairs : List (Bool × Bool)) :
    (result base reject inputLeft outputLeft inputAfter outputAfter pairs).1.outputTape.current =
      some (decide (pairs.map Prod.fst = pairs.map Prod.snd)) := by
  induction pairs generalizing base inputLeft outputLeft with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      by_cases same : first = second
      · subst second
        simpa [result] using ih (base + 5) (some first :: inputLeft) (some first :: outputLeft)
      · simp [result, same, stopped, Tape.write]

end CryptoOracle.Interactive.NativeCompareBlock
