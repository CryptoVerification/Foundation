import Foundation.Crypto.Semantics.Machine.FixedWidthOutputPadding
import Foundation.Crypto.Semantics.Machine.OutputColumnRewind
import Foundation.Crypto.Semantics.Machine.ConsumedInputErasure
import Foundation.Crypto.Semantics.Machine.SavedBitstringRewind
import Foundation.Crypto.Semantics.Machine.NativeSequence

namespace Machine.ScalarSamplePadding

private def eraseModulus : Program := eraseOutputBlock.swapTapes

/-- After acceptance, rewind the sampled output, erase the old modulus
without touching its protected width counter, rewind that counter, and use
it to write the high zero padding. Each stage runs on the returned tapes. -/
def program : Program :=
  ((OutputColumnRewind.toFirst.followedBy eraseModulus).followedBy rewindBitstring).followedBy
    FixedWidthOutputPadding.program

theorem runs (width : Nat) (modulus sample : List Bool)
    (hModulus : modulus.length ≤ width) (hSample : sample.length ≤ width) :
    ∃ (target : Configuration) (used : Nat), used ≤ 13*width+17 ∧
      RunsFor program
        ({ inputTape := { left := modulus.reverse.map some ++ none :: List.replicate width (some true) }
           outputTape := { left := sample.reverse.map some } } : Configuration)
        target used ∧ target.halted = true ∧
      target.outputBits = Binary.encode width (Binary.value sample) := by
  let counterBits := List.replicate width true
  let counter := List.replicate width (some true)
  let modulusTape : Tape := { left := modulus.reverse.map some ++ none::counter }
  obtain ⟨u, hu, firstRun, firstOutput⟩ := OutputColumnRewind.toFirst_runs sample modulusTape
  let rewound := (rewindBitstringFinish sample modulusTape).swapTapes
  have firstHalt : rewound.halted = true := rfl
  have firstInput : rewound.inputTape = modulusTape := rfl
  have eraseRun := (eraseOutputBlock_runs rewound.outputTape counter modulus []).swapTapes
  let erased := (eraseOutputBlockFinish rewound.outputTape counter modulus []).swapTapes
  have eraseLayout : (eraseOutputBlockStart rewound.outputTape counter modulus []).swapTapes.Equivalent
      (rewound.resumeAt 0) := Configuration.Equivalent.refl _
  obtain ⟨actualErase, v, hv, linked₁, halt₁, input₁, output₁⟩ :=
    firstRun.followedBy_equivalent eraseRun eraseLayout (Nat.zero_le _) rfl firstHalt rfl
  have erasedInput : erased.inputTape =
      { left := counter, right := List.replicate (modulus.length+1) none } := by
    change ({ left := counter, right := List.replicate (modulus.reverse.length+1) none ++ [] } : Tape) = _
    simp
  have erasedOutput : erased.outputTape = rewound.outputTape := rfl
  have rewindRun := rewindBitstring_runs_saved counterBits [] none
    (List.replicate (modulus.length+1) none) rewound.outputTape
  have rewindLayout :
      ({ inputTape := { left := counterBits.reverse.map some ++ [none], right := List.replicate (modulus.length+1) none }
         outputTape := rewound.outputTape } : Configuration).Equivalent (actualErase.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have boundary := (ConsumedInputErasure.outer_blank counterBits).symm
      have same :
          ({ left := counterBits.reverse.map some ++ [none], right := List.replicate (modulus.length+1) none } : Tape).Equivalent
            { left := counter, right := List.replicate (modulus.length+1) none } := by
        refine ⟨rfl, ?_, fun _ => rfl⟩
        simpa [counter, counterBits] using boundary.2.1
      exact same.trans (by simpa only [erased, erasedInput, Configuration.resumeAt] using input₁)
    · simpa only [erased, erasedOutput, Configuration.resumeAt] using output₁
  obtain ⟨actualCounter, z, hz, linked₂, halt₂, input₂, output₂⟩ :=
    linked₁.followedBy_equivalent rewindRun rewindLayout (Nat.zero_le _) rfl halt₁ rfl
  have outer : ({ Tape.ofBits counterBits with left := [none] } : Tape).Equivalent (Tape.ofBits counterBits) := by
    refine ⟨rfl, ?_, fun _ => rfl⟩
    intro i
    cases i <;> cases counterBits <;> rfl
  have counterInput : actualCounter.inputTape.Equivalent (Tape.ofBits counterBits) :=
    input₂.symm.trans ((rewindBitstring_saved_input_equivalent counterBits [] (modulus.length+1)).trans outer)
  have counterOutput : actualCounter.outputTape.Equivalent (Tape.ofBits sample) := output₂.symm.trans firstOutput
  obtain ⟨padded, t, ht, padRun, padHalt, padOutput⟩ := FixedWidthOutputPadding.runs_encoded width sample hSample
  have padLayout :
      ({ inputTape := Tape.ofBits counterBits, outputTape := Tape.ofBits sample } : Configuration).Equivalent
        (actualCounter.resumeAt 0) := ⟨rfl, rfl, counterInput.symm, counterOutput.symm⟩
  obtain ⟨target, used, hUsed, run, hHalt, _, hOutput⟩ :=
    linked₂.followedBy_equivalent padRun padLayout (Nat.zero_le _) rfl halt₂ padHalt
  refine ⟨target, used, ?_, ?_, hHalt, hOutput.bits.symm.trans padOutput⟩
  · simp only [counterBits, List.length_replicate] at hz
    omega
  · exact run

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · apply Program.followedBy_no_randomBit
      · intro selected; cases selected <;> decide
      · exact Program.swapTapes_no_randomBit _ eraseOutputBlock_no_randomBit
    · exact rewindBitstring_no_randomBit
  · exact FixedWidthOutputPadding.no_randomBit

/-- Fixed-budget evaluation of the physical padding code from any retained
cell-equivalent accepted layout. Redundant blanks do not reload either tape. -/
theorem eval_from_layout (width : Nat) (modulus sample : List Bool)
    (hModulus : modulus.length ≤ width) (hSample : sample.length ≤ width)
    (start : Configuration) (hPc : start.pc = 0) (hActive : start.halted = false)
    (hInput : start.inputTape.Equivalent
      {left := modulus.reverse.map some ++ none::List.replicate width (some true)})
    (hOutput : start.outputTape.Equivalent {left := sample.reverse.map some}) :
    ∃ finish : Configuration, finish.halted = true ∧
      finish.outputBits = Binary.encode width (Binary.value sample) ∧
      evalConfigWithin program start (13*width+17) = PMF.pure finish := by
  obtain ⟨canonical, used, hUsed, run, hHalt, hBits⟩ := runs width modulus sample hModulus hSample
  obtain ⟨finish, actualRun, same⟩ := run.exists_equivalent
    (⟨hPc.symm, hActive.symm, hInput.symm, hOutput.symm⟩ : _)
  have finishHalt : finish.halted = true := same.2.1.symm.trans hHalt
  have atUsed := actualRun.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit
  have allStopped (target : Configuration) (trace : PaddedRunsFor program start target used) :
      target.halted = true := by
    have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [atUsed] at member
    have identical : target = finish := by simpa using member
    exact identical ▸ finishHalt
  exact ⟨finish, finishHalt, same.outputBits.symm.trans hBits,
    (evalConfigWithin_eq_of_le program start used (13*width+17) hUsed allStopped).trans atUsed⟩

end Machine.ScalarSamplePadding
