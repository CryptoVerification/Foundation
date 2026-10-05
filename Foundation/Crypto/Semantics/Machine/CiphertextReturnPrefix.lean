import Foundation.Crypto.Semantics.Machine.FramedModulusColumnPreparation
import Foundation.Crypto.Semantics.Machine.FixedWidthFieldSkip
import Foundation.Crypto.Semantics.Machine.InstanceBaseCopy
import Foundation.Crypto.Semantics.Machine.InstanceExponentCopy
import Foundation.Crypto.Semantics.Machine.ContextualInput

namespace Machine.CiphertextReturnPrefix

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

/-- Locate the first ciphertext component using native parsing and
four repetitions of the physical width counter. The two powers and product
remain on the input, while the modulus columns supply the framing width. -/
def program : Program :=
  ((((FramedModulusColumnPreparation.program.followedBy OutputColumnRewind.thirdBoundaryToFirst).followedBy
    FixedWidthFieldSkip.program).followedBy FixedWidthFieldSkip.program).followedBy
    FixedWidthFieldSkip.program).followedBy FixedWidthFieldSkip.program

theorem runs_valid (n : Nat) (modulus scalar generator publicKey message firstComponent shared secondComponent : List Bool)
    (hModulus : modulus.length = n+3)
    (hScalar : scalar.length = modulus.length) (hGenerator : generator.length = modulus.length)
    (hKey : publicKey.length = modulus.length) (hMessage : message.length = modulus.length) :
    let instanceBits := modulus++scalar++generator++publicKey++message
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ firstComponent ++ shared ++ secondComponent
    let before := instanceBits.reverse.map some ++
      some false::List.replicate instanceBits.length (some true) ++ some false::List.replicate n (some true)
    ∃ target used, used ≤ 1000*(n+3) ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {Tape.ofBits (firstComponent++shared++secondComponent) with left := before} ∧
      target.outputTape.Equivalent (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus)) := by
  dsimp only
  let inst := modulus++scalar++generator++publicKey++message
  let raw := encodeSecurityParameter n ++ frame inst ++ firstComponent ++ shared ++ secondComponent
  let header := some false::List.replicate inst.length (some true) ++ some false::List.replicate n (some true)
  let b0 := modulus.reverse.map some ++ header
  let b1 := scalar.reverse.map some ++ b0
  let b2 := generator.reverse.map some ++ b1
  let b3 := publicKey.reverse.map some ++ b2
  let b4 := message.reverse.map some ++ b3
  let template := BinaryThirdColumnTemplate.columns modulus
  let tracks := modulus.map (fun bit => ((false,false),bit))
  have templateEq : BinaryModularAddition.interleave tracks = template := rfl
  have tracksLength : tracks.length = modulus.length := by simp [tracks]
  have templateLength : template.length = 3*modulus.length := BinaryThirdColumnTemplate.columns_length _
  obtain ⟨prepared,a,ha,prep,hPrep,inpPrep,outPrep⟩ :=
    FramedModulusColumnPreparation.runs_valid n modulus (scalar++generator++publicKey++message)
      (firstComponent++shared++secondComponent) hModulus
  let initialInput : Tape := {Tape.ofBits (scalar++generator++publicKey++message++firstComponent++shared++secondComponent) with left := b0}
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
    (generator++publicKey++message++firstComponent++shared++secondComponent) (hScalar.trans tracksLength.symm) b0
  rw [templateEq] at r1 o1
  obtain ⟨v1,t1,ht1,run1,halt1,in1,out1⟩ := append readyRun r1 rfl rfl readyHalt
    (by simpa [initialInput,List.append_assoc] using readyInp) readyOut h1 i1 o1
  obtain ⟨s2,d,hd,r2,h2,i2,o2⟩ := FixedWidthFieldSkip.runs tracks generator
    (publicKey++message++firstComponent++shared++secondComponent) (hGenerator.trans tracksLength.symm) b1
  rw [templateEq] at r2 o2
  obtain ⟨v2,t2,ht2,run2,halt2,in2,out2⟩ := append run1 r2 rfl rfl halt1
    (by simpa [b1,List.append_assoc] using in1) out1 h2 i2 o2
  obtain ⟨s3,e,he,r3,h3,i3,o3⟩ := FixedWidthFieldSkip.runs tracks publicKey
    (message++firstComponent++shared++secondComponent) (hKey.trans tracksLength.symm) b2
  rw [templateEq] at r3 o3
  obtain ⟨v3,t3,ht3,run3,halt3,in3,out3⟩ := append run2 r3 rfl rfl halt2
    (by simpa [b2,List.append_assoc] using in2) out2 h3 i3 o3
  obtain ⟨s4,e4,he4,r4,h4,i4,o4⟩ := FixedWidthFieldSkip.runs tracks message
    (firstComponent++shared++secondComponent) (hMessage.trans tracksLength.symm) b3
  rw [templateEq] at r4 o4
  obtain ⟨target,used,bound,run,halt,inp,out⟩ := append run3 r4 rfl rfl halt3
    (by simpa [b3,List.append_assoc] using in3) out3 h4 i4 o4
  refine ⟨target,used,?_,?_,halt,?_,out⟩
  · rw [templateEq,templateLength,tracksLength] at hc hd he he4
    change b ≤ 2*template.length+9 at hb
    rw [templateLength] at hb
    simp only [List.length_append,hScalar,hGenerator,hKey,hMessage,hModulus] at ha
    omega
  · simpa only [program,raw,inst,List.append_assoc] using run
  · simpa [b4,b3,b2,b1,b0,header,inst,List.reverse_append,List.map_append,List.append_assoc] using inp

private theorem modulusNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ FramedModulusColumnPreparation.program := by
  cases tape <;> decide

private theorem thirdNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ OutputColumnRewind.thirdBoundaryToFirst := by
  cases tape <;> decide

private theorem secondNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ OutputColumnRewind.secondBoundaryToFirst := by
  cases tape <;> decide

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  unfold program
  exact (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ modulusNoRandom thirdNoRandom) FixedWidthFieldSkip.no_randomBit) FixedWidthFieldSkip.no_randomBit) FixedWidthFieldSkip.no_randomBit) FixedWidthFieldSkip.no_randomBit) tape

end Machine.CiphertextReturnPrefix
