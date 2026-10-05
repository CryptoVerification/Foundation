import Foundation.Crypto.Semantics.Machine.FramedModulusColumnPreparation
import Foundation.Crypto.Semantics.Machine.InstanceExponentCopy

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Machine.FramedExponentPreparation

private def firstReturn : Nat := FramedModulusColumnPreparation.program.length + 1
private def secondReturn : Nat := firstReturn + OutputColumnRewind.thirdBoundaryToFirst.length + 1
private def finalReturn : Nat := secondReturn + InstanceExponentCopy.program.length + 1
private def first : Program := FramedModulusColumnPreparation.program.asSubroutine 0 firstReturn
private def second : Program := OutputColumnRewind.thirdBoundaryToFirst.asSubroutine firstReturn secondReturn

/-- Read the instance modulus into the third track, rewind the physical
columns, and copy the following unframed exponent into the second track.
The instance generator and response frame remain on the input tape. -/
def program : Program := first ++ second ++
  InstanceExponentCopy.program.asSubroutine secondReturn finalReturn ++ [.halt]

private theorem first_layout : program =
    Program.withSubroutine [] FramedModulusColumnPreparation.program
      (second ++ InstanceExponentCopy.program.asSubroutine secondReturn finalReturn ++ [.halt]) firstReturn := by
  simp [program, first, Program.withSubroutine, List.append_assoc]

private theorem second_layout : program =
    Program.withSubroutine first OutputColumnRewind.thirdBoundaryToFirst
      (InstanceExponentCopy.program.asSubroutine secondReturn finalReturn ++ [.halt]) secondReturn := by
  simp [program, second, first, firstReturn, Program.withSubroutine,
    Program.asSubroutine_length, List.append_assoc]

private theorem third_layout : program =
    Program.withSubroutine (first ++ second) InstanceExponentCopy.program [.halt] finalReturn := by
  simp [program, second, secondReturn, first, firstReturn, Program.withSubroutine,
    Program.asSubroutine_length, Nat.add_assoc]

private theorem final_step (actual : Configuration)
    (hPc : actual.pc = finalReturn) (hActive : actual.halted = false) :
    Step program actual { actual with halted := true } := by
  have hLookup : program[finalReturn]? = some .halt := by
    rw [third_layout]
    have hIndex : finalReturn = (first ++ second).length + InstanceExponentCopy.program.length + 1 + 0 := by
      simp [finalReturn, secondReturn, firstReturn, first, second,
        Program.asSubroutine_length, Nat.add_assoc]
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

def validBudget (n : Nat) (modulus exponent generator : List Bool) : Nat :=
  (9 * n + 21 + 2 * (3 * (n + 3)) + 8 +
    (3 * ((modulus ++ exponent ++ generator).length + 1) + 9 * modulus.length + 2) + 1) +
    (2 * (BinaryThirdColumnTemplate.columns modulus).length + 9) +
    (9 * exponent.length + 5) + 1

/-- The two populated arithmetic tracks come from the actual framed
instance. Both tapes are inherited at each call; the unexamined generator
and reply have not been reconstructed or decoded by a machine primitive. -/
theorem runs_valid (n : Nat) (modulus exponent generator following : List Bool)
    (hModulus : modulus.length = n + 3)
    (hExponent : exponent.length = modulus.length) :
    let instanceBits := modulus ++ exponent ++ generator
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ following
    let before := modulus.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true)
    ∃ target used, used ≤ validBudget n modulus exponent generator ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits (generator ++ following) with left := exponent.reverse.map some ++ before } ∧
      target.outputTape.Equivalent
        { left := none :: (BinaryColumnSlotFill.fullSlots
          (List.replicate modulus.length false) exponent modulus).reverse.map some } := by
  dsimp only
  let instanceBits := modulus ++ exponent ++ generator
  let before := modulus.reverse.map some ++
    some false :: List.replicate instanceBits.length (some true) ++
      some false :: List.replicate n (some true)
  let columns := BinaryThirdColumnTemplate.columns modulus
  obtain ⟨prepared, u₁, hu₁, run₁, hHalt₁, hInput₁, hOutput₁⟩ :=
    FramedModulusColumnPreparation.runs_valid n modulus (exponent ++ generator) following hModulus
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedModulusColumnPreparation.program
    (second ++ InstanceExponentCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ following))
      (prepared.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa [instanceBits, Configuration.rebasePc, List.append_assoc] using embedded₁
  obtain ⟨rewound, u₂, hu₂, run₂, hHalt₂, hInput₂, hOutput₂⟩ :=
    OutputColumnRewind.thirdBoundaryToFirst_runs columns prepared.inputTape
  let idealRewind : Configuration :=
    { inputTape := prepared.inputTape, outputTape := { left := none :: none :: columns.reverse.map some } }
  let actualRewind : Configuration := { inputTape := prepared.inputTape, outputTape := prepared.outputTape }
  have hRewind : idealRewind.Equivalent actualRewind :=
    ⟨rfl, rfl, Tape.Equivalent.refl _, hOutput₁.symm⟩
  obtain ⟨actualRewound, actualRun₂, hRewound⟩ := run₂.exists_equivalent hRewind
  obtain ⟨v₂, hv₂, embedded₂⟩ := actualRun₂.withSubroutine_halted
    first OutputColumnRewind.thirdBoundaryToFirst
    (InstanceExponentCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl (hRewound.2.1.symm.trans hHalt₂)
  have r₂ : RunsFor program (prepared.resumeAt firstReturn)
      (actualRewound.resumeAt secondReturn) v₂ := by
    rw [second_layout]
    simpa [first, firstReturn, Program.asSubroutine_length,
      Configuration.rebasePc, Configuration.resumeAt, actualRewind] using embedded₂
  obtain ⟨copied, u₃, hu₃, run₃, hHalt₃, hInput₃, hOutput₃⟩ :=
    InstanceExponentCopy.runs_exponent exponent modulus (generator ++ following) hExponent before
  let canonical : Configuration :=
    { inputTape := { Tape.ofBits (exponent ++ (generator ++ following)) with left := before },
      outputTape := Tape.ofBits columns }
  change RunsFor InstanceExponentCopy.program canonical copied u₃ at run₃
  have hCall : (canonical.rebasePc (first ++ second).length).Equivalent
      (actualRewound.resumeAt secondReturn) := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp [canonical, Configuration.rebasePc, Configuration.resumeAt, first, second,
        firstReturn, secondReturn, Program.asSubroutine_length, Nat.add_assoc]
    · have hIdeal : prepared.inputTape.Equivalent canonical.inputTape := by
        simpa [canonical, before, instanceBits, List.append_assoc] using hInput₁
      have hPhysical : rewound.inputTape.Equivalent actualRewound.inputTape := hRewound.2.2.1
      rw [hInput₂] at hPhysical
      exact hIdeal.symm.trans hPhysical
    · exact hOutput₂.symm.trans hRewound.2.2.2
  obtain ⟨v₃, hv₃, embedded₃⟩ := run₃.withSubroutine_halted
    (first ++ second) InstanceExponentCopy.program [.halt] finalReturn
    (Nat.zero_le _) rfl hHalt₃
  have sourceEmbedded : RunsFor program (canonical.rebasePc (first ++ second).length)
      (copied.resumeAt finalReturn) v₃ := by rw [third_layout]; exact embedded₃
  obtain ⟨actual, r₃, hResult⟩ := sourceEmbedded.exists_equivalent hCall
  have hPc : actual.pc = finalReturn := by simpa [Configuration.resumeAt] using hResult.1.symm
  have hActive : actual.halted = false := hResult.2.1.symm
  refine ⟨{ actual with halted := true }, v₁ + v₂ + v₃ + 1, ?_,
    ((r₁.trans r₂).trans r₃).succ (final_step actual hPc hActive), rfl, ?_, ?_⟩
  · dsimp only [validBudget]
    dsimp only [columns] at hu₂
    simp only [List.length_append] at hu₁ ⊢
    omega
  · exact hResult.2.2.1.symm.trans (hInput₃ ▸ Tape.Equivalent.refl _)
  · exact hResult.2.2.2.symm.trans (hOutput₃ ▸ Tape.Equivalent.refl _)

/-- No malformed request can turn either the rewind or the payload loop
into an unbounded scan. The input suffix remains contiguous and finite. -/
theorem runs_any_suffix (raw : List Bool) :
    ∃ target used remaining before, used ≤ 10000 * (raw.length + 1) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape = { Tape.ofBits remaining with left := before } ∧ remaining.length ≤ raw.length := by
  obtain ⟨prepared, u₁, remaining₁, before₁, hu₁, run₁, hHalt₁, hInput₁, hLength₁⟩ :=
    FramedModulusColumnPreparation.runs_any_suffix raw
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] FramedModulusColumnPreparation.program
    (second ++ InstanceExponentCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
    firstReturn (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (prepared.resumeAt firstReturn) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨rewound, u₂, hu₂, run₂, hHalt₂, hInput₂⟩ :=
    OutputColumnRewind.thirdBoundaryToFirst_runs_any prepared.inputTape prepared.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted
    first OutputColumnRewind.thirdBoundaryToFirst
    (InstanceExponentCopy.program.asSubroutine secondReturn finalReturn ++ [.halt])
    secondReturn (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (prepared.resumeAt firstReturn) (rewound.resumeAt secondReturn) v₂ := by
    rw [second_layout]
    simpa [first, firstReturn, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  obtain ⟨copied, remaining, before, u₃, hu₃, run₃, hHalt₃, hInput₃, hLength₃⟩ :=
    InstanceExponentCopy.runs_any before₁ remaining₁ rewound.outputTape
  have hInput : rewound.inputTape = { Tape.ofBits remaining₁ with left := before₁ } :=
    hInput₂.trans hInput₁
  change RunsFor InstanceExponentCopy.program
    ({ inputTape := { Tape.ofBits remaining₁ with left := before₁ },
       outputTape := rewound.outputTape } : Configuration) copied u₃ at run₃
  rw [← hInput] at run₃
  obtain ⟨v₃, hv₃, embedded₃⟩ := run₃.withSubroutine_halted
    (first ++ second) InstanceExponentCopy.program [.halt] finalReturn
    (Nat.zero_le _) rfl hHalt₃
  have r₃ : RunsFor program (rewound.resumeAt secondReturn) (copied.resumeAt finalReturn) v₃ := by
    rw [third_layout]
    simpa [first, second, firstReturn, secondReturn,
      Program.asSubroutine_length, Configuration.resumeAt, Configuration.rebasePc,
      Nat.add_assoc] using embedded₃
  have hStorage := GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length + 2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  have hLeft : prepared.outputTape.left.length ≤ prepared.outputTape.cells := by simp [Tape.cells]; omega
  simp only [GuardedCompiler.sourceStorage] at hStorage hInitial
  refine ⟨{ copied.resumeAt finalReturn with halted := true }, v₁ + v₂ + v₃ + 1,
    remaining, before, by omega,
    ((r₁.trans r₂).trans r₃).succ (final_step _ rfl rfl), rfl, hInput₃, by omega⟩

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (10000 * (raw.length + 1)) := by
  obtain ⟨target, used, remaining, before, hUsed, run, hHalt, _hInput, _hLength⟩ := runs_any_suffix raw
  exact run.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 10000 * (length + 1),
    (PolynomiallyBounded.const 10000).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.FramedExponentPreparation
