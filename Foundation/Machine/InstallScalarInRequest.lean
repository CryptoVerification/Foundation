import Foundation.Machine.AdvanceInputByOutput
import Foundation.Machine.OverwriteInputField
import Foundation.Machine.OutputColumnRewind
import Foundation.Machine.UnaryInput
import Foundation.Machine.NativeSequence

namespace Machine.InstallScalarInRequest

/-- Read both real unary headers, cross the modulus using the sampled
scalar as a physical width counter, then copy that same scalar into the
request's middle field. The generator and scalar source are retained. -/
def program : Program :=
  (((skipUnary.followedBy skipUnary).followedBy AdvanceInputByOutput.program).followedBy
    OutputColumnRewind.toFirst).followedBy OverwriteInputField.program

theorem runs (n : Nat) (modulus order generator scalar : List Bool)
    (hModulus : modulus.length = scalar.length) (hOrder : order.length = scalar.length) :
    let instanceBits := modulus++order++generator
    let before := modulus.reverse.map some ++ some false::
      (List.replicate instanceBits.length (some true) ++ some false::List.replicate n (some true))
    ∃ target used, used ≤ 3*n+3*instanceBits.length+12*scalar.length+20 ∧
      RunsFor program
        ({inputTape := Tape.ofBits (encodeSecurityParameter n ++ frame instanceBits),
          outputTape := Tape.ofBits scalar} : Configuration) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        {Tape.ofBits generator with left := scalar.reverse.map some ++ before} ∧
      target.outputTape.Equivalent {left := scalar.reverse.map some} := by
  dsimp only
  let instanceBits := modulus++order++generator
  let header := some false::List.replicate n (some true)
  let payloadBefore := some false::(List.replicate instanceBits.length (some true) ++ header)
  let before := modulus.reverse.map some ++ payloadBefore
  have scalarLeft : {Tape.ofBits scalar with left := []} = Tape.ofBits scalar := by
    cases scalar <;> rfl
  have rawLeft : {Tape.ofBits (encodeSecurityParameter n ++ frame instanceBits) with left := []} =
      Tape.ofBits (encodeSecurityParameter n ++ frame instanceBits) := by
    cases h : encodeSecurityParameter n ++ frame instanceBits <;> rfl
  have first := skipUnary_runs [] n (frame instanceBits) (Tape.ofBits scalar)
  have second := skipUnary_runs header instanceBits.length instanceBits (Tape.ofBits scalar)
  have join : skipUnaryStart header instanceBits.length instanceBits (Tape.ofBits scalar) =
      (skipUnaryFinish [] n (frame instanceBits) (Tape.ofBits scalar)).resumeAt 0 := by
    simp [skipUnaryStart, skipUnaryFinish, header, frame, encodeSecurityParameter,
      Configuration.resumeAt]
  obtain ⟨headers, u, hu, headersRun, headersHalt, headersInput, headersOutput⟩ :=
    first.followedBy_equivalent second (join ▸ Configuration.Equivalent.refl _)
      (Nat.zero_le _) rfl rfl rfl
  have advance := AdvanceInputByOutput.runs payloadBefore [] modulus (order++generator) scalar hModulus
  simp only [AdvanceInputByOutput.start, scalarLeft] at advance
  have advanceLayout :
      ({inputTape := {Tape.ofBits (modulus++(order++generator)) with left := payloadBefore},
        outputTape := Tape.ofBits scalar} : Configuration).Equivalent (headers.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [skipUnaryFinish, instanceBits, payloadBefore, List.append_assoc, Configuration.resumeAt] using (show _ from headersInput)
    · simpa [skipUnaryFinish, Configuration.resumeAt] using headersOutput
  obtain ⟨positioned, v, hv, positionedRun, positionedHalt, positionedInput, positionedOutput⟩ :=
    headersRun.followedBy_equivalent advance advanceLayout (Nat.zero_le _) rfl headersHalt rfl
  let input : Tape := {Tape.ofBits (order++generator) with left := before}
  have rewindRun := OutputColumnRewind.toFirst_runs scalar input
  obtain ⟨w, hw, rewindRun, rewindOutput⟩ := rewindRun
  have rewindLayout :
      (rewindBitstringStart scalar input).swapTapes.Equivalent (positioned.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [AdvanceInputByOutput.finish, before, input, Configuration.resumeAt, rewindBitstringStart, Configuration.swapTapes] using positionedInput
    · simpa [AdvanceInputByOutput.finish, rewindBitstringStart, Configuration.swapTapes, Configuration.resumeAt] using positionedOutput
  obtain ⟨rewound, z, hz, rewoundRun, rewoundHalt, rewoundInput, rewoundSaved⟩ :=
    positionedRun.followedBy_equivalent rewindRun rewindLayout (Nat.zero_le _) rfl positionedHalt rfl
  have overwrite := OverwriteInputField.runs before [] order generator scalar hOrder
  simp only [OverwriteInputField.start, scalarLeft] at overwrite
  have overwriteLayout :
      ({inputTape := input, outputTape := Tape.ofBits scalar} : Configuration).Equivalent
        (rewound.resumeAt 0) := by
    refine ⟨rfl, rfl, rewoundInput, ?_⟩
    exact rewindOutput.symm.trans rewoundSaved
  obtain ⟨target, used, bound, run, halted, inputResult, outputResult⟩ :=
    rewoundRun.followedBy_equivalent overwrite overwriteLayout (Nat.zero_le _) rfl rewoundHalt rfl
  refine ⟨target, used, ?_, ?_, halted, ?_, ?_⟩
  · simp only [instanceBits] at hu ⊢
    omega
  · simpa only [program, skipUnaryStart, rawLeft] using run
  · simpa [OverwriteInputField.finish, before, payloadBefore, header, instanceBits] using inputResult.symm
  · simpa [OverwriteInputField.finish] using outputResult.symm

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · apply Program.followedBy_no_randomBit
      · exact Program.followedBy_no_randomBit _ _ skipUnary_no_randomBit skipUnary_no_randomBit
      · exact AdvanceInputByOutput.no_randomBit
    · intro selected; cases selected <;> decide
  · exact OverwriteInputField.no_randomBit


end Machine.InstallScalarInRequest
