import Foundation.Crypto.Semantics.Machine.FramedModulusColumnPreparation
import Foundation.Crypto.Semantics.Machine.FixedWidthFieldSkip
import Foundation.Crypto.Semantics.Machine.InstanceBaseCopy
import Foundation.Crypto.Semantics.Machine.InstanceExponentCopy
import Foundation.Crypto.Semantics.Machine.ContextualInput

namespace Machine.FramedCiphertextProductInput

private def positioned (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

private theorem append {first second : Program} {start middle finish : Configuration}
    {u v : Nat} {input output nextInput nextOutput : Tape}
    (one : RunsFor first start middle u)
    (two : RunsFor second (positioned input output) finish v)
    (active : start.halted = false) (pc : start.pc = 0) (stopped : middle.halted = true)
    (inputEq : middle.inputTape.Equivalent input) (outputEq : middle.outputTape.Equivalent output)
    (lastHalt : finish.halted = true)
    (lastInput : finish.inputTape.Equivalent nextInput)
    (lastOutput : finish.outputTape.Equivalent nextOutput) :
    ∃ target used, used ≤ u+v+1 ∧ RunsFor (first.followedBy second) start target used ∧
      target.halted = true ∧ target.inputTape.Equivalent nextInput ∧
      target.outputTape.Equivalent nextOutput := by
  have boundary : (positioned input output).Equivalent (middle.resumeAt 0) :=
    ⟨rfl,rfl,inputEq.symm,outputEq.symm⟩
  obtain ⟨target,used,bound,run,halt,inp,out⟩ :=
    one.followedBy_equivalent two boundary (by rw [pc]; exact Nat.zero_le _) active stopped lastHalt
  exact ⟨target,used,bound,run,halt,inp.symm.trans lastInput,out.symm.trans lastOutput⟩

/-- Build the multiplication columns by physically reading the retained
message and shared power. The intermediate scalar and both power results
remain on the input tape until the final product has been calculated. -/
def program : Program :=
  (((((((((FramedModulusColumnPreparation.program.followedBy OutputColumnRewind.thirdBoundaryToFirst).followedBy
    FixedWidthFieldSkip.program).followedBy FixedWidthFieldSkip.program).followedBy
    FixedWidthFieldSkip.program).followedBy InstanceBaseCopy.program).followedBy
    OutputColumnRewind.toFirst).followedBy FixedWidthFieldSkip.program).followedBy
    InstanceExponentCopy.program).followedBy GuardedCompiler.seekScratchInput).followedBy
    OutputColumnRewind.secondBoundaryToFirst

theorem runs_valid (n : Nat) (modulus scalar generator publicKey message firstComponent shared : List Bool)
    (hModulus : modulus.length = n+3)
    (hScalar : scalar.length = modulus.length) (hGenerator : generator.length = modulus.length)
    (hKey : publicKey.length = modulus.length) (hMessage : message.length = modulus.length)
    (hFirst : firstComponent.length = modulus.length) (hShared : shared.length = modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus++scalar++generator++publicKey++message) ++ firstComponent ++ shared
    let columns := BinaryColumnSlotFill.fullSlots message shared modulus
    ∃ target used, used ≤ 1000*(n+3) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {left := none::raw.reverse.map some} ∧
      target.outputTape.Equivalent (Tape.ofBits columns) := by
  dsimp only
  let inst := modulus++scalar++generator++publicKey++message
  let raw := encodeSecurityParameter n ++ frame inst ++ firstComponent ++ shared
  let header := some false::List.replicate inst.length (some true) ++ some false::List.replicate n (some true)
  let b0 := modulus.reverse.map some ++ header
  let b1 := scalar.reverse.map some ++ b0
  let b2 := generator.reverse.map some ++ b1
  let b3 := publicKey.reverse.map some ++ b2
  let b4 := message.reverse.map some ++ b3
  let b5 := firstComponent.reverse.map some ++ b4
  let b6 := shared.reverse.map some ++ b5
  let template := BinaryThirdColumnTemplate.columns modulus
  let tracks := modulus.map (fun bit => ((false,false),bit))
  let firstTracks := (message.zip modulus).map (fun pair => ((pair.1,false),pair.2))
  let firstBits := BinaryColumnSlotFill.firstSlots message modulus
  let columns := BinaryColumnSlotFill.fullSlots message shared modulus
  have templateEq : BinaryModularAddition.interleave tracks = template := rfl
  have firstEq : BinaryModularAddition.interleave firstTracks = firstBits := rfl
  have tracksLength : tracks.length = modulus.length := by simp [tracks]
  have firstTracksLength : firstTracks.length = modulus.length := by simp [firstTracks,hMessage]
  have templateLength : template.length = 3*modulus.length := by
    exact BinaryThirdColumnTemplate.columns_length _
  have firstLength : firstBits.length = 3*modulus.length := by
    have len (cs : List BinaryModularAddition.Column) : (BinaryModularAddition.interleave cs).length = 3*cs.length := by
      induction cs with
      | nil => rfl
      | cons c cs ih => simp [BinaryModularAddition.interleave,ih]; omega
    simpa [firstBits,BinaryColumnSlotFill.firstSlots,hMessage] using len ((message.zip modulus).map (fun pair => ((pair.1,false),pair.2)))
  obtain ⟨prepared,a,ha,prep,hPrep,inpPrep,outPrep⟩ :=
    FramedModulusColumnPreparation.runs_valid n modulus (scalar++generator++publicKey++message)
      (firstComponent++shared) hModulus
  let initialInput : Tape := {Tape.ofBits (scalar++generator++publicKey++message++firstComponent++shared) with left := b0}
  obtain ⟨rewound,b,hb,rewind,hRewind,inpRewind,outRewind⟩ :=
    OutputColumnRewind.thirdBoundaryToFirst_runs template initialInput
  have rewindStart : (positioned initialInput {left := none::none::template.reverse.map some}).Equivalent (prepared.resumeAt 0) := by
    refine ⟨rfl,rfl,?_,outPrep.symm⟩
    simpa [initialInput,b0,header,inst,List.append_assoc,Configuration.resumeAt,positioned] using inpPrep.symm
  obtain ⟨ready,ab,hab,readyRun,readyHalt,readyInput,readyOutput⟩ :=
    prep.followedBy_equivalent rewind rewindStart (Nat.zero_le _) rfl hPrep hRewind
  have readyInp : ready.inputTape.Equivalent initialInput := by
    simpa only [inpRewind] using readyInput.symm
  have readyOut := readyOutput.symm.trans outRewind
  obtain ⟨s1,c,hc,r1,h1,i1,o1⟩ := FixedWidthFieldSkip.runs tracks scalar
    (generator++publicKey++message++firstComponent++shared) (hScalar.trans tracksLength.symm) b0
  rw [templateEq] at r1 o1
  obtain ⟨v1,t1,ht1,run1,halt1,in1,out1⟩ := append readyRun r1 rfl rfl readyHalt
    (by simpa [initialInput,List.append_assoc] using readyInp) readyOut h1 i1 o1
  obtain ⟨s2,d,hd,r2,h2,i2,o2⟩ := FixedWidthFieldSkip.runs tracks generator
    (publicKey++message++firstComponent++shared) (hGenerator.trans tracksLength.symm) b1
  rw [templateEq] at r2 o2
  obtain ⟨v2,t2,ht2,run2,halt2,in2,out2⟩ := append run1 r2 rfl rfl halt1
    (by simpa [b1,List.append_assoc] using in1) out1 h2 i2 o2
  obtain ⟨s3,e,he,r3,h3,i3,o3⟩ := FixedWidthFieldSkip.runs tracks publicKey
    (message++firstComponent++shared) (hKey.trans tracksLength.symm) b2
  rw [templateEq] at r3 o3
  obtain ⟨v3,t3,ht3,run3,halt3,in3,out3⟩ := append run2 r3 rfl rfl halt2
    (by simpa [b2,List.append_assoc] using in2) out2 h3 i3 o3
  obtain ⟨filled,f,hf,fill,hFill,fillInput,fillOutput⟩ :=
    InstanceBaseCopy.runs_first_template message modulus (firstComponent++shared) hMessage b3
  obtain ⟨v4,t4,ht4,run4,halt4,in4,out4⟩ := append run3 fill rfl rfl halt3
    (by simpa [b3,List.append_assoc] using in3) out3 hFill
    (by rw [fillInput]; exact Tape.Equivalent.refl _) (by rw [fillOutput]; exact Tape.Equivalent.refl _)
  let nextInput : Tape := {Tape.ofBits (firstComponent++shared) with left := b4}
  obtain ⟨j,hj,re,reOut⟩ := OutputColumnRewind.toFirst_runs firstBits nextInput
  have reRun : RunsFor OutputColumnRewind.toFirst
      (positioned nextInput {left := firstBits.reverse.map some})
      (rewindBitstringFinish firstBits nextInput).swapTapes j := re
  obtain ⟨v5,t5,ht5,run5,halt5,in5,out5⟩ := append run4 reRun rfl rfl halt4
    (by simpa [nextInput,b4] using in4) out4 rfl (Tape.Equivalent.refl _) reOut
  obtain ⟨su,k,hk,skipU,hU,iu,ou⟩ := FixedWidthFieldSkip.runs firstTracks firstComponent shared
    (hFirst.trans firstTracksLength.symm) b4
  rw [firstEq] at skipU ou
  obtain ⟨v6,t6,ht6,run6,halt6,in6,out6⟩ := append run5 skipU rfl rfl halt5
    (by simpa [nextInput,rewindBitstringFinish,Configuration.swapTapes] using in5) out5 hU iu ou
  obtain ⟨ex,l,hl,exRun,exHalt,exInput,exOutput⟩ :=
    InstanceExponentCopy.runs_into_first message shared modulus [] hMessage hShared b5
  obtain ⟨v7,t7,ht7,run7,halt7,in7,out7⟩ := append run6 exRun rfl rfl halt6
    (by simpa [b5] using in6) out6 exHalt
    (by rw [exInput]; exact Tape.Equivalent.refl _) (by rw [exOutput]; exact Tape.Equivalent.refl _)
  have seek := seekBitstringNext_runs b6 [] [] {left := none::columns.reverse.map some}
  have seekEq : seekBitstringNextStart b6 [] [] {left := none::columns.reverse.map some} =
      positioned {left := b6} {left := none::columns.reverse.map some} := by
    simp [seekBitstringNextStart_layout,Tape.ofBits,Tape.moveRight,positioned]
  rw [seekEq] at seek
  obtain ⟨v8,t8,ht8,run8,halt8,in8,out8⟩ := append run7 seek rfl rfl halt7
    (by simpa [b6,Tape.ofBits] using in7) out7 rfl (Tape.Equivalent.refl _) (Tape.Equivalent.refl _)
  obtain ⟨last,z,hz,lastRun,lastHalt,lastInput,lastOutput⟩ :=
    OutputColumnRewind.secondBoundaryToFirst_runs columns {left := none::b6}
  have lastStart : RunsFor OutputColumnRewind.secondBoundaryToFirst
      (positioned {left := none::b6} {left := none::columns.reverse.map some}) last z := lastRun
  obtain ⟨target,used,bound,run,halt,inp,out⟩ := append run8 lastStart rfl rfl halt8
    (by simpa [seekBitstringNextFinish_layout_cells,Tape.moveRight] using in8)
    (by simpa [seekBitstringNextFinish_layout_cells] using out8) lastHalt
    (by simpa [lastInput] using Tape.Equivalent.refl ({left := none::b6} : Tape)) lastOutput
  refine ⟨target,used,?_,?_,halt,?_,out⟩
  · rw [templateEq,templateLength,tracksLength] at hc hd he
    rw [firstEq,firstLength,firstTracksLength] at hk
    simp only [List.length_append,hScalar,hGenerator,hKey,hMessage,hFirst,hShared,hModulus] at ha hf hl
    change b ≤ 2*template.length+9 at hb
    change j ≤ 2*firstBits.length+4 at hj
    change z ≤ 2*columns.length+7 at hz
    have colLen : columns.length = 3*modulus.length := by
      simp [columns,BinaryColumnSlotFill.fullSlots_length,hMessage,hShared]
    rw [templateLength] at hb
    rw [firstLength] at hj
    rw [colLen] at hz
    simp only [List.length_nil] at ht8
    omega
  · simpa only [program,raw,inst,List.append_assoc] using run
  · have same : b6 = raw.reverse.map some := by
      simp [b6,b5,b4,b3,b2,b1,b0,header,raw,inst,frame,encodeSecurityParameter,
        List.reverse_append,List.map_append,List.append_assoc]
    simpa only [same] using inp

private theorem modulusNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ FramedModulusColumnPreparation.program := by
  cases tape <;> decide

private theorem thirdNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ OutputColumnRewind.thirdBoundaryToFirst := by
  cases tape <;> decide

private theorem secondNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ OutputColumnRewind.secondBoundaryToFirst := by
  cases tape <;> decide

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  unfold program
  exact (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ modulusNoRandom thirdNoRandom) FixedWidthFieldSkip.no_randomBit) FixedWidthFieldSkip.no_randomBit) FixedWidthFieldSkip.no_randomBit) InstanceBaseCopy.no_randomBit) OutputColumnRewind.toFirst_no_randomBit) FixedWidthFieldSkip.no_randomBit) InstanceExponentCopy.no_randomBit) GuardedCompiler.seekScratchInput_no_randomBit) secondNoRandom) tape

end Machine.FramedCiphertextProductInput
