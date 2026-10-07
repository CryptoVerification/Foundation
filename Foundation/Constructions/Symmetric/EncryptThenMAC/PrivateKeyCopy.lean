import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! A native private-buffer operation for reduction controllers. The input
tape is a private key store; the output tape is a private response buffer.
This code copies a contiguous key into that buffer and restores the key head.
It must not be run with the adversary's public output tape as its destination.
Every copied cell, head movement, branch, and final halt is charged. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivateKeyCopy
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def code : Program :=
  [.branch .input 8 1 3,
   .write .output false, .jump 5,
   .write .output true, .jump 5,
   .moveRight .input, .moveRight .output, .jump 0,
   .moveLeft .input, .branch .input 10 8 8,
   .moveRight .input, .halt]

def copying (before remaining : List Bool) (outputBefore : List (Option Bool)) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := before.reverse.map some },
    outputTape := { left := outputBefore } }

def rewinding (left : List Bool) (current : Option Bool) (right : List (Option Bool))
    (output : Tape) : Configuration :=
  { pc := 8, inputTape := ⟨left.map some, current, right⟩, outputTape := output }

def restored (cells : List (Option Bool)) : Tape :=
  ⟨[none], cells.headD none, cells.tail⟩

theorem copy_cell (bit : Bool) (before remaining : List Bool)
    (outputBefore : List (Option Bool)) :
    evalConfigWithin code (copying before (bit :: remaining) outputBefore) 6 =
      PMF.pure (copying (before ++ [bit]) remaining (some bit :: outputBefore)) := by
  cases bit <;> cases remaining <;>
    simp [evalConfigWithin, stepPMF, next, code, copying, Tape.ofBits,
      Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight, List.reverse_append]

theorem copy_loop (before remaining : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin code (copying before remaining outputBefore) (6 * remaining.length + 1) =
      PMF.pure (rewinding (before ++ remaining).reverse none []
        { left := remaining.reverse.map some ++ outputBefore }) := by
  induction remaining generalizing before outputBefore with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, code, copying, rewinding, Tape.ofBits,
        Instruction.next, Configuration.tape]
  | cons bit remaining ih =>
      rw [show 6 * (bit :: remaining).length + 1 = 6 + (6 * remaining.length + 1) by simp; omega,
        evalConfigWithin_add, copy_cell, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind_cell (bit : Bool) (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin code (rewinding (bit :: left) current right output) 2 =
      PMF.pure (rewinding left (some bit) (current :: right) output) := by
  cases bit <;>
    simp [evalConfigWithin, stepPMF, next, code, rewinding, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveLeft]

theorem rewind_loop (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin code (rewinding left current right output) (2 * left.length + 4) =
      PMF.pure ({ pc := 11, inputTape := restored (left.reverse.map some ++ current :: right), outputTape := output, halted := true } : Configuration) := by
  induction left generalizing current right with
  | nil =>
      simp [evalConfigWithin, stepPMF, next, code, rewinding, restored, Instruction.next,
        Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveLeft, Tape.moveRight]
  | cons bit left ih =>
      rw [show 2 * (bit :: left).length + 4 = 2 + (2 * left.length + 4) by simp; omega,
        evalConfigWithin_add, rewind_cell, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def finish (key : List Bool) (outputBefore : List (Option Bool)) : Configuration :=
  { pc := 11, halted := true, inputTape := restored (key.map some ++ [none]),
    outputTape := { left := key.reverse.map some ++ outputBefore } }

/-- The entire physical configuration is specified. The key is traversed and
rewound, while the existing private response prefix remains on its tape. -/
theorem run (key : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin code (copying [] key outputBefore) (8 * key.length + 5) =
      PMF.pure (finish key outputBefore) := by
  rw [show 8 * key.length + 5 = (6 * key.length + 1) + (2 * key.reverse.length + 4) by simp; omega,
    evalConfigWithin_add, copy_loop, PMF.pure_bind]
  simpa [finish] using rewind_loop key.reverse none []
    ({ left := key.reverse.map some ++ outputBefore } : Tape)

private theorem getD_append_blank (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell cells ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i

/-- The restored head and every relative key cell agree with the original
key store. Extra represented blank cells do not constitute a free tape reset. -/
theorem key_restored (key : List Bool) (outputBefore : List (Option Bool)) :
    (finish key outputBefore).inputTape.Equivalent (Tape.ofBits key) := by
  cases key with
  | nil =>
      refine ⟨rfl, ?_, fun _ => rfl⟩
      intro i
      cases i <;> simp [finish, restored, Tape.ofBits]
  | cons bit key =>
      refine ⟨rfl, ?_, ?_⟩
      · intro i
        cases i <;> simp [finish, restored, Tape.ofBits]
      · intro i
        exact getD_append_blank (key.map some) i

theorem output_bits (key header : List Bool) :
    (finish key (header.reverse.map some)).outputBits = header ++ key := by
  simp [finish, Configuration.outputBits, Tape.bits, List.reverse_append,
    List.map_reverse, List.filterMap_append, List.filterMap_map]

theorem key_bits (key : List Bool) (outputBefore : List (Option Bool)) :
    (finish key outputBefore).inputTape.bits = key := by
  rw [(key_restored key outputBefore).bits]
  cases key <;> simp [Tape.ofBits, Tape.bits, List.filterMap_map]

theorem halts (key : List Bool) : HaltsWithin code key (8 * key.length + 5) := by
  intro final trace
  have hm := (mem_support_evalConfigWithin_iff code (Configuration.initial key) final (8 * key.length + 5)).mpr trace
  have hStart : Configuration.initial key = copying [] key [] := by
    cases key <;> rfl
  rw [hStart] at hm
  rw [run, PMF.mem_support_pure_iff] at hm
  subst final
  rfl

theorem joint_run (key header : List Bool) :
    (evalConfigWithin code (copying [] key (header.reverse.map some)) (8 * key.length + 5)).map
      (fun final => (final.halted, final.inputTape.bits, final.outputBits)) =
        PMF.pure (true, key, header ++ key) := by
  rw [run, PMF.pure_map, key_bits, output_bits]
  rfl

/-- Restored stores may retain blank padding after a previous call. Running
the same finite code again gives the same joint observations, at the same
bound; the proof does not normalize the physical store before execution. -/
theorem reusable_run (key header : List Bool) (store : Tape)
    (hStore : store.Equivalent (Tape.ofBits key)) :
    (evalConfigWithin code
      { inputTape := store, outputTape := { left := header.reverse.map some } }
      (8 * key.length + 5)).map
        (fun final => (final.halted, final.inputTape.bits, final.outputBits)) =
          PMF.pure (true, key, header ++ key) := by
  have hInput : store.Equivalent (copying [] key (header.reverse.map some)).inputTape := by
    cases key <;> simpa [copying, Tape.ofBits] using hStore
  have hConfig : ({ inputTape := store, outputTape := { left := header.reverse.map some } } : Configuration).Equivalent
      (copying [] key (header.reverse.map some)) :=
    ⟨rfl, rfl, hInput, Tape.Equivalent.refl _⟩
  rw [evalConfigWithin_map_eq_of_equivalent code _ _ hConfig _ _
    (fun first second h => by rw [h.2.1, h.2.2.1.bits, h.outputBits])]
  exact joint_run key header

end Foundation.Symmetric.EncryptThenMAC.PrivateKeyCopy
