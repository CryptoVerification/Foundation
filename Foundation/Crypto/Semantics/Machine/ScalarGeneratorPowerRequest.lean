import Foundation.Crypto.Semantics.Machine.RestoreSavedScalarRequest
import Foundation.Crypto.Semantics.Machine.InstallScalarInRequest
import Foundation.Crypto.Semantics.Machine.RewindInputSuffix

namespace Machine.ScalarGeneratorPowerRequest

/-- Install a sampled scalar into the saved public request and restore the
modified request's start. The duplicate scalar output is physically erased
only after its bits are retained as the request's exponent. -/
def program : Program :=
  (((RestoreSavedScalarRequest.program.followedBy OutputColumnRewind.toFirst).followedBy
    InstallScalarInRequest.program).followedBy rewindBitstring).followedBy eraseOutputBlock

theorem runs_nonempty_generator (n : Nat) (modulus order generator scalar : List Bool)
    (hModulus : modulus.length = n+3)
    (hOrder : order.length = modulus.length)
    (hGenerator : generator ≠ [])
    (hScalar : scalar.length = modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus++order++generator)
    let modified := encodeSecurityParameter n ++ frame (modulus++scalar++generator)
    ∃ target used, used ≤ 20*raw.length+40*(n+3)+100 ∧
      RunsFor program
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some},
          outputTape := {left := scalar.reverse.map some}} : Configuration) target used ∧
      target.halted = true ∧ target.inputTape.Equivalent (Tape.ofBits modified) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (modulus++order++generator)
  let instanceBits := modulus++order++generator
  let modified := encodeSecurityParameter n ++ frame (modulus++scalar++generator)
  let prefixBits := encodeSecurityParameter n ++ List.replicate instanceBits.length true ++ [false] ++ modulus ++ scalar
  obtain ⟨restored, u, hu, restoreRun, restoreHalt, restoreInput, restoreOutput⟩ :=
    RestoreSavedScalarRequest.runs (n+3) raw {left := scalar.reverse.map some}
  obtain ⟨v, hv, rewindOutput, scalarFirst⟩ := OutputColumnRewind.toFirst_runs scalar (Tape.ofBits raw)
  have firstJoin : (rewindBitstringStart scalar (Tape.ofBits raw)).swapTapes.Equivalent
      (restored.resumeAt 0) := ⟨rfl, rfl, restoreInput.symm, restoreOutput.symm⟩
  obtain ⟨first, x, hx, firstRun, firstHalt, firstInput, firstOutput⟩ :=
    restoreRun.followedBy_equivalent rewindOutput firstJoin (Nat.zero_le _) rfl restoreHalt rfl
  obtain ⟨installed, t, ht, installRun, installHalt, installInput, installOutput⟩ :=
    InstallScalarInRequest.runs n modulus order generator scalar hScalar.symm
      (hOrder.trans hScalar.symm)
  have secondJoin :
      ({inputTape := Tape.ofBits raw, outputTape := Tape.ofBits scalar} : Configuration).Equivalent
        (first.resumeAt 0) := by
    refine ⟨rfl, rfl, firstInput, ?_⟩
    exact scalarFirst.symm.trans firstOutput
  obtain ⟨second, y, hy, secondRun, secondHalt, secondInput, secondOutput⟩ :=
    firstRun.followedBy_equivalent installRun secondJoin (Nat.zero_le _) rfl firstHalt installHalt
  have prefixNonempty : prefixBits ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    simp [prefixBits, encodeSecurityParameter] at length
  have generatorNonempty := hGenerator
  have prefixCells : prefixBits.reverse.map some = scalar.reverse.map some ++
      modulus.reverse.map some ++ some false::(List.replicate instanceBits.length (some true) ++
        some false::List.replicate n (some true)) := by
    simp [prefixBits, encodeSecurityParameter, List.reverse_append, List.map_append, List.append_assoc]
  obtain ⟨rewound, rewindInputRun, rewindInputHalt, packet, preserved⟩ :=
    rewindBitstring_runs_suffix prefixBits generator {left := scalar.reverse.map some} prefixNonempty generatorNonempty
  have thirdJoin :
      ({inputTape := {Tape.ofBits generator with left := prefixBits.reverse.map some},
        outputTape := {left := scalar.reverse.map some}} : Configuration).Equivalent (second.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · rw [prefixCells]
      simpa [instanceBits, List.append_assoc, Configuration.resumeAt] using installInput.symm.trans secondInput
    · exact installOutput.symm.trans secondOutput
  obtain ⟨third, z, hz, thirdRun, thirdHalt, thirdInput, thirdOutput⟩ :=
    secondRun.followedBy_equivalent rewindInputRun thirdJoin (Nat.zero_le _) rfl secondHalt rewindInputHalt
  have modifiedEq : prefixBits++generator = modified := by
    simp [prefixBits, modified, frame, instanceBits, hOrder, hScalar, List.append_assoc]
  rw [modifiedEq] at packet
  have eraseRun := eraseOutputBlock_runs (Tape.ofBits modified) [] scalar []
  have fourthJoin : (eraseOutputBlockStart (Tape.ofBits modified) [] scalar []).Equivalent
      (third.resumeAt 0) := by
    refine ⟨rfl, rfl, packet.symm.trans thirdInput, ?_⟩
    change ({left := scalar.reverse.map some ++ [none]} : Tape).Equivalent (third.resumeAt 0).outputTape
    exact (ConsumedInputErasure.outer_blank scalar).symm.trans (by simpa only [preserved, Configuration.resumeAt] using thirdOutput)
  obtain ⟨target, used, bound, run, halted, inputResult, outputResult⟩ :=
    thirdRun.followedBy_equivalent eraseRun fourthJoin (Nat.zero_le _) rfl thirdHalt rfl
  refine ⟨target, used, ?_, run, halted, inputResult.symm, ?_⟩
  · have rawLength : raw.length = n+1+2*instanceBits.length+1 := by
      simp [raw, instanceBits, frame, encodeSecurityParameter]; omega
    have prefixLength : prefixBits.length ≤ raw.length := by
      have prefLength : prefixBits.length = n+2+instanceBits.length+modulus.length+scalar.length := by
        simp [prefixBits, encodeSecurityParameter]; omega
      have instLength : instanceBits.length = modulus.length+order.length+generator.length := by
        simp [instanceBits]; omega
      omega
    change used ≤ 20*raw.length+40*(n+3)+100
    change t ≤ 3*n+3*instanceBits.length+12*scalar.length+20 at ht
    omega
  · have blank := Tape.blank_padding_equivalent ([] : List (Option Bool)) (scalar.length+1)
    have eraserBlank : (eraseOutputBlockFinish (Tape.ofBits modified) [] scalar []).outputTape.Equivalent ({} : Tape) := by
      change ({right := List.replicate (scalar.reverse.length+1) none ++ []} : Tape).Equivalent _
      simpa using blank
    exact outputResult.symm.trans eraserBlank

theorem runs (n : Nat) (modulus order generator scalar : List Bool)
    (hModulus : modulus.length = n+3)
    (hOrder : order.length = modulus.length)
    (hGenerator : generator.length = modulus.length)
    (hScalar : scalar.length = modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus++order++generator)
    let modified := encodeSecurityParameter n ++ frame (modulus++scalar++generator)
    ∃ target used, used ≤ 20*raw.length+40*(n+3)+100 ∧
      RunsFor program
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some},
          outputTape := {left := scalar.reverse.map some}} : Configuration) target used ∧
      target.halted = true ∧ target.inputTape.Equivalent (Tape.ofBits modified) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  apply runs_nonempty_generator n modulus order generator scalar hModulus hOrder _ hScalar
  intro empty
  simp [empty] at hGenerator
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · apply Program.followedBy_no_randomBit
      · exact Program.followedBy_no_randomBit _ _ RestoreSavedScalarRequest.no_randomBit OutputColumnRewind.toFirst_no_randomBit
      · exact InstallScalarInRequest.no_randomBit
    · exact rewindBitstring_no_randomBit
  · exact eraseOutputBlock_no_randomBit

end Machine.ScalarGeneratorPowerRequest
