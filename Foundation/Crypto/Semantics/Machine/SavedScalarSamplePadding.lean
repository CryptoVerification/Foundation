import Foundation.Crypto.Semantics.Machine.ScalarSamplePadding

namespace Machine.ScalarSamplePadding

/-- The actual padding code preserves public caller data below the saved
width counter. This is a retained-tape execution, not a subsequent reload. -/
theorem runs_saved_layout (before : List (Option Bool)) (width : Nat) (modulus sample : List Bool)
    (hModulus : modulus.length ≤ width) (hSample : sample.length ≤ width) :
    ∃ (target : Configuration) (used : Nat), used ≤ 13*width+17 ∧
      RunsFor program
        ({ inputTape := { left := modulus.reverse.map some ++ none :: (List.replicate width (some true) ++ none::before) }
           outputTape := { left := sample.reverse.map some } } : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {left := List.replicate width (some true) ++ none::before} ∧
      target.outputBits = Binary.encode width (Binary.value sample) ∧
      target.outputTape.Equivalent {left := (Binary.encode width (Binary.value sample)).reverse.map some} := by
  let counterBits := List.replicate width true
  let counter := List.replicate width (some true) ++ none::before
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
  have rewindRun := rewindBitstring_runs_saved counterBits before none
    (List.replicate (modulus.length+1) none) rewound.outputTape
  have rewindLayout :
      ({ inputTape := { left := counterBits.reverse.map some ++ none::before, right := List.replicate (modulus.length+1) none }
         outputTape := rewound.outputTape } : Configuration).Equivalent (actualErase.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have same :
          ({ left := counterBits.reverse.map some ++ none::before,
             right := List.replicate (modulus.length+1) none } : Tape) =
            { left := counter, right := List.replicate (modulus.length+1) none } := by
        simp [counter, counterBits]
      rw [same]
      simpa only [erased, erasedInput, Configuration.resumeAt] using input₁
    · simpa only [erased, erasedOutput, Configuration.resumeAt] using output₁
  obtain ⟨actualCounter, z, hz, linked₂, halt₂, input₂, output₂⟩ :=
    linked₁.followedBy_equivalent rewindRun rewindLayout (Nat.zero_le _) rfl halt₁ rfl
  have counterInput : actualCounter.inputTape.Equivalent
      {Tape.ofBits counterBits with left := none::before} :=
    input₂.symm.trans (rewindBitstring_saved_input_equivalent counterBits before (modulus.length+1))
  have counterOutput : actualCounter.outputTape.Equivalent (Tape.ofBits sample) := output₂.symm.trans firstOutput
  obtain ⟨padded, t, ht, padRun, padHalt, padInput, padOutput, padTape⟩ := FixedWidthOutputPadding.runs_encoded_saved_layout before width sample hSample
  have padLayout :
      ({ inputTape := {Tape.ofBits counterBits with left := none::before}, outputTape := Tape.ofBits sample } : Configuration).Equivalent
        (actualCounter.resumeAt 0) := ⟨rfl, rfl, counterInput.symm, counterOutput.symm⟩
  obtain ⟨target, used, hUsed, run, hHalt, hInput, hOutput⟩ :=
    linked₂.followedBy_equivalent padRun padLayout (Nat.zero_le _) rfl halt₂ padHalt
  refine ⟨target, used, ?_, ?_, hHalt, ?_, hOutput.bits.symm.trans padOutput, ?_⟩
  · simp only [counterBits, List.length_replicate] at hz
    omega
  · exact run
  · rw [padInput] at hInput
    exact hInput.symm
  · rw [padTape] at hOutput
    exact hOutput.symm


theorem runs_saved (before : List (Option Bool)) (width : Nat) (modulus sample : List Bool)
    (hModulus : modulus.length ≤ width) (hSample : sample.length ≤ width) :
    ∃ (target : Configuration) (used : Nat), used ≤ 13*width+17 ∧
      RunsFor program
        ({ inputTape := { left := modulus.reverse.map some ++ none :: (List.replicate width (some true) ++ none::before) }
           outputTape := { left := sample.reverse.map some } } : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {left := List.replicate width (some true) ++ none::before} ∧
      target.outputBits = Binary.encode width (Binary.value sample) := by
  obtain ⟨target, used, bound, run, halted, input, bits, _⟩ :=
    runs_saved_layout before width modulus sample hModulus hSample
  exact ⟨target, used, bound, run, halted, input, bits⟩

/-- Fixed-budget evaluation of the physical padding code from any retained
cell-equivalent accepted layout. Redundant blanks do not reload either tape. -/
theorem eval_from_layout_saved (before : List (Option Bool)) (width : Nat) (modulus sample : List Bool)
    (hModulus : modulus.length ≤ width) (hSample : sample.length ≤ width)
    (start : Configuration) (hPc : start.pc = 0) (hActive : start.halted = false)
    (hInput : start.inputTape.Equivalent
      {left := modulus.reverse.map some ++ none::(List.replicate width (some true) ++ none::before)})
    (hOutput : start.outputTape.Equivalent {left := sample.reverse.map some}) :
    ∃ finish : Configuration, finish.halted = true ∧
      finish.outputBits = Binary.encode width (Binary.value sample) ∧
      evalConfigWithin program start (13*width+17) = PMF.pure finish := by
  obtain ⟨canonical, used, hUsed, run, hHalt, _, hBits⟩ := runs_saved before width modulus sample hModulus hSample
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
