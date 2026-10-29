import Foundation.Crypto.Semantics.Machine.SubroutineAtHalt

/-! Read and consume a real input cell, then execute one of two native programs.
The return halt is charged and both inherited tapes are retained. -/
namespace Machine.NativeBitChoice
open Foundation.Probability

def returnPc (zero one : Program) : Nat := zero.length + one.length + 5

def zeroPrefix (zero one : Program) : Program :=
  [.branch .input (returnPc zero one) 1 (zero.length + 3), .moveRight .input]

def onePrefix (zero one : Program) : Program :=
  zeroPrefix zero one ++ zero.asSubroutine 2 (returnPc zero one) ++ [.moveRight .input]

def suffix (zero one : Program) : Program :=
  [.moveRight .input] ++ one.asSubroutine (zero.length + 4) (returnPc zero one) ++ [.halt]

def code (zero one : Program) : Program :=
  Program.withSubroutine (zeroPrefix zero one) zero (suffix zero one) (returnPc zero one)

theorem code_length (zero one : Program) :
    (code zero one).length = zero.length + one.length + 6 := by
  simp [code, Program.withSubroutine, zeroPrefix, suffix]
  omega

theorem onePrefix_length (zero one : Program) :
    (onePrefix zero one).length = zero.length + 4 := by
  simp [onePrefix, zeroPrefix]

theorem code_one_layout (zero one : Program) :
    code zero one =
      Program.withSubroutine (onePrefix zero one) one [.halt] (returnPc zero one) := by
  simp only [code, Program.withSubroutine, onePrefix, suffix]
  simp [zeroPrefix, List.append_assoc]

theorem code_return_halt (zero one : Program) :
    (code zero one)[returnPc zero one]? = some .halt := by
  rw [code_one_layout]
  have h := Program.withSubroutine_getElem?_suffix (onePrefix zero one) one [.halt]
    (returnPc zero one) 0
  simpa [onePrefix_length, returnPc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def start (input output : Tape) : Configuration :=
  {inputTape := input, outputTape := output}

def consumed (input output : Tape) : Configuration :=
  {inputTape := input.moveRight, outputTape := output}

theorem zero_prefix_run (zero one : Program) (input output : Tape)
    (hbit : input.current = some false) :
    evalConfigWithin (code zero one) (start input output) 2 =
      PMF.pure ((consumed input output).rebasePc 2) := by
  have h0 : (code zero one)[0]? =
      some (.branch .input (returnPc zero one) 1 (zero.length + 3)) := rfl
  have h1 : (code zero one)[1]? = some (.moveRight .input) := rfl
  simp [evalConfigWithin, stepPMF, next, Instruction.next, start, consumed,
    Configuration.tape, Configuration.updateTape, Configuration.advance,
    Configuration.rebasePc, hbit, h0, h1]

theorem one_prefix_run (zero one : Program) (input output : Tape)
    (hbit : input.current = some true) :
    evalConfigWithin (code zero one) (start input output) 2 =
      PMF.pure ((consumed input output).rebasePc (zero.length + 4)) := by
  have h0 : (code zero one)[0]? =
      some (.branch .input (returnPc zero one) 1 (zero.length + 3)) := rfl
  have ht : (code zero one)[zero.length + 3]? = some (.moveRight .input) := by
    have h := Program.withSubroutine_getElem?_suffix (zeroPrefix zero one) zero
      (suffix zero one) (returnPc zero one) 0
    simpa [code, zeroPrefix, suffix, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  simp [evalConfigWithin, stepPMF, next, Instruction.next, start, consumed,
    Configuration.tape, Configuration.updateTape, Configuration.advance,
    Configuration.rebasePc, hbit, h0, ht, Nat.add_assoc]

theorem run_zero (zero one : Program) (input output : Tape)
    (hbit : input.current = some false) (steps : Nat)
    (halts : ∀ finish, PaddedRunsFor zero (consumed input output) finish steps →
      finish.halted = true) :
    evalConfigWithin (code zero one) (start input output) (steps + 3) =
      (evalConfigWithin zero (consumed input output) steps).map
        (fun c => {c with pc := returnPc zero one, halted := true}) := by
  rw [show steps + 3 = 2 + (steps + 1) by omega, evalConfigWithin_add,
    zero_prefix_run zero one input output hbit, PMF.pure_bind]
  have hLayout : ∀ pc, pc ≤ zero.length →
      (zeroPrefix zero one).length + pc ≠ returnPc zero one := by
    intro pc hp
    simp only [zeroPrefix, List.length_cons, List.length_nil] at *
    unfold returnPc
    omega
  exact Program.evalConfigWithin_withSubroutine_haltAt
    (zeroPrefix zero one) zero (suffix zero one) (returnPc zero one)
    hLayout (code_return_halt zero one) (consumed input output) (by simp [consumed])
    rfl steps halts

theorem run_one (zero one : Program) (input output : Tape)
    (hbit : input.current = some true) (steps : Nat)
    (halts : ∀ finish, PaddedRunsFor one (consumed input output) finish steps →
      finish.halted = true) :
    evalConfigWithin (code zero one) (start input output) (steps + 3) =
      (evalConfigWithin one (consumed input output) steps).map
        (fun c => {c with pc := returnPc zero one, halted := true}) := by
  rw [show steps + 3 = 2 + (steps + 1) by omega, evalConfigWithin_add,
    one_prefix_run zero one input output hbit, PMF.pure_bind, code_one_layout]
  have h := Program.evalConfigWithin_withSubroutine_final_halt
    (onePrefix zero one) one (consumed input output) (by simp [consumed]) rfl steps halts
  simpa [onePrefix_length, returnPc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem halts_zero (zero one : Program) (input output : Tape)
    (hbit : input.current = some false) (steps : Nat)
    (halts : ∀ finish, PaddedRunsFor zero (consumed input output) finish steps →
      finish.halted = true) :
    ∀ finish, PaddedRunsFor (code zero one) (start input output) finish (steps + 3) →
      finish.halted = true := by
  intro finish run
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [run_zero zero one input output hbit steps halts, PMF.mem_support_map_iff] at member
  obtain ⟨c, _, rfl⟩ := member
  rfl

theorem halts_one (zero one : Program) (input output : Tape)
    (hbit : input.current = some true) (steps : Nat)
    (halts : ∀ finish, PaddedRunsFor one (consumed input output) finish steps →
      finish.halted = true) :
    ∀ finish, PaddedRunsFor (code zero one) (start input output) finish (steps + 3) →
      finish.halted = true := by
  intro finish run
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [run_one zero one input output hbit steps halts, PMF.mem_support_map_iff] at member
  obtain ⟨c, _, rfl⟩ := member
  rfl

end Machine.NativeBitChoice
