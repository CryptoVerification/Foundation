import Foundation.Crypto.Semantics.Machine.BinaryWorkspaceAppend
import Foundation.Crypto.Semantics.Machine.NativeInvocation

namespace Machine.BinaryWorkspacePreparation

private def pre : Program := BinaryWorkspaceAppend.program.asSubroutine 0 11

/-- One fixed finite code scans the raw request, writes the high zero
column, rewinds the same input tape, and halts. The two stages are linked
through their actual returned configurations. -/
def program : Program :=
  Program.withSubroutine pre rewindBitstring [.halt] 16

private theorem layout : program =
    Program.withSubroutine [] BinaryWorkspaceAppend.program
      (rewindBitstring.asSubroutine 11 16 ++ [.halt]) 11 := by
  simp [program, pre, Program.withSubroutine, Program.asSubroutine_length]
  rfl

def budget (length : Nat) : Nat := 5 * length + 19

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  simp only [program, Program.withSubroutine, pre, List.mem_append, not_or]
  exact ⟨⟨Program.asSubroutine_no_randomBit _ BinaryWorkspaceAppend.no_randomBit _ _ tape,
    Program.asSubroutine_no_randomBit _ rewindBitstring_no_randomBit _ _ tape⟩, by simp⟩

/-- The actual halted input layout, including the outer blank cells left
by rewind. -/
def finish (bits : List Bool) : Configuration :=
  { (rewindBitstringFinish (bits ++ [false, false, false]) ({} : Tape)).resumeAt 16 with
    halted := true }

/-- Every finite raw input is padded and rewound within a linear native
step bound. In particular, malformed/truncated triples still terminate. -/
theorem runs (bits : List Bool) :
    ∃ used, used ≤ budget bits.length ∧
      RunsFor program (Configuration.initial bits) (finish bits) used := by
  let padded := bits ++ [false, false, false]
  obtain ⟨u1, hu1, r1⟩ := (BinaryWorkspaceAppend.runs bits).withSubroutine_halted
    [] BinaryWorkspaceAppend.program
    (rewindBitstring.asSubroutine 11 16 ++ [.halt]) 11
    (by change 0 ≤ 10; omega) rfl rfl
  rw [← layout] at r1
  obtain ⟨u2, hu2, r2⟩ := (rewindBitstring_runs padded ({} : Tape)).withSubroutine_halted
    pre rewindBitstring [.halt] 16
    (by change 0 ≤ 4; omega) rfl rfl
  change RunsFor program _ _ u2 at r2
  have hJoin : (BinaryWorkspaceAppend.finish bits).resumeAt 11 =
      (rewindBitstringStart padded ({} : Tape)).rebasePc pre.length := by
    rfl
  rw [hJoin] at r1
  have hLast : Step program
      ((rewindBitstringFinish padded ({} : Tape)).resumeAt 16) (finish bits) := by
    have hLookup : program[16]? = some .halt := by
      change (Program.withSubroutine pre rewindBitstring [.halt] 16)[16]? = some .halt
      have hOffset : 16 = pre.length + rewindBitstring.length + 1 + 0 := by rfl
      rw [hOffset, Program.withSubroutine_getElem?_suffix]
      rfl
    simp [Step, successors, next, finish, Instruction.next, hLookup,
      Configuration.resumeAt, padded]
  refine ⟨u1 + u2 + 1, ?_, (r1.trans r2).succ hLast⟩
  change u1 + u2 + 1 ≤ 5 * bits.length + 19
  simp only [padded, List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add] at hu2
  omega

/-- The padding and rewind trace also works when caller data are stored
behind a blank to the left of the raw input. The saved cells remain on the
physical tape throughout the run. -/
theorem runs_with_saved (bits : List Bool) (before : List (Option Bool)) :
    ∃ target used, used ≤ budget bits.length ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits bits with left := none :: before } } : Configuration)
        target used ∧
      target.halted = true ∧
      target.inputTape =
        ({ left := before,
           right := (bits ++ [false, false, false]).map some ++ [none] } : Tape).moveRight ∧
      target.outputTape = ({} : Tape) := by
  let padded := bits ++ [false, false, false]
  let appended : Configuration :=
    { pc := 9, inputTape := { left := padded.reverse.map some ++ none :: before },
      halted := true }
  obtain ⟨u1, hu1, r1⟩ :=
    (BinaryWorkspaceAppend.runs_with_saved bits (none :: before)).withSubroutine_halted
      [] BinaryWorkspaceAppend.program
      (rewindBitstring.asSubroutine 11 16 ++ [.halt]) 11
      (by change 0 ≤ 10; omega) rfl rfl
  rw [← layout] at r1
  let rewound := rewindScratchFinish before padded ({} : Tape)
  obtain ⟨u2, hu2, r2⟩ :=
    (rewindScratch_runs_from before padded none [] ({} : Tape)).withSubroutine_halted
      pre rewindBitstring [.halt] 16
      (by change 0 ≤ 4; omega) rfl rfl
  change RunsFor program _ _ u2 at r2
  have hJoin : appended.resumeAt 11 =
      (rewindScratchStart before padded ({} : Tape)).rebasePc pre.length := by
    rfl
  rw [hJoin] at r1
  have hLast : Step program (rewound.resumeAt 16)
      { rewound.resumeAt 16 with halted := true } := by
    have hLookup : program[16]? = some .halt := by
      change (Program.withSubroutine pre rewindBitstring [.halt] 16)[16]? = some .halt
      have hOffset : 16 = pre.length + rewindBitstring.length + 1 + 0 := by rfl
      rw [hOffset, Program.withSubroutine_getElem?_suffix]
      rfl
    simp [Step, successors, next, Configuration.resumeAt, Instruction.next, hLookup]
  refine ⟨{ rewound.resumeAt 16 with halted := true }, u1 + u2 + 1,
    ?_, (r1.trans r2).succ hLast, rfl, ?_, ?_⟩
  · change u1 + u2 + 1 ≤ 5 * bits.length + 19
    simp only [padded, List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add] at hu2
    omega
  · rfl
  · rfl

private theorem map_append_blank_getD (bits : List Bool) (i : Nat) :
    (bits.map some ++ [none]).getD i none = (bits.map some).getD i none := by
  induction bits generalizing i with
  | nil => cases i <;> rfl
  | cons bit bits ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.map_cons, List.cons_append,
          List.getD_cons_succ] using ih i

theorem saved_input_equivalent (bits : List Bool) (before : List (Option Bool)) :
    (({ left := before,
        right := (bits ++ [false, false, false]).map some ++ [none] } : Tape).moveRight).Equivalent
      { Tape.ofBits (bits ++ [false, false, false]) with left := none :: before } := by
  let padded := bits ++ [false, false, false]
  have h : ({ left := before, right := padded.map some ++ [none] } : Tape).Equivalent
      { left := before, right := padded.map some } := by
    exact ⟨rfl, fun _ => rfl, map_append_blank_getD padded⟩
  have hMove := h.moveRight
  have hLayout : ({ left := before, right := padded.map some } : Tape).moveRight =
      { Tape.ofBits padded with left := none :: before } := by
    cases padded <;> rfl
  simpa only [padded, hLayout] using hMove

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  obtain ⟨used, hUsed, run⟩ := runs bits
  exact run.haltsFrom_of_no_randomBit (by rfl) no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, (PolynomiallyBounded.const 5).mul PolynomiallyBounded.id |>.add
    (PolynomiallyBounded.const 19), haltsWithin⟩

/-- The rewound input cells are exactly the padded raw request, up to
represented outer blanks. This equivalence is a proof relation, not a
run-time tape normalization. -/
theorem finish_input (bits : List Bool) :
    (finish bits).inputTape.Equivalent
      (Tape.ofBits (bits ++ [false, false, false])) := by
  simpa only [finish, Configuration.inputTape, Configuration.resumeAt] using
    rewindBitstringFinish_input_equivalent (bits ++ [false, false, false]) ({} : Tape)

end Machine.BinaryWorkspacePreparation
