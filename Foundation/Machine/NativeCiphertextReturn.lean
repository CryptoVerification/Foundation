import Foundation.Machine.CiphertextReturnPrefix
import Foundation.Machine.FixedWidthColumnFrame
import Foundation.Machine.CiphertextSecondReturn

namespace Machine.NativeCiphertextReturn
open FixedWidthScalarReturn

/-- Return exactly the first power and final modular product, in the
ciphertext's specified order. The shared power is traversed but not returned. -/
def program : Program := (CiphertextReturnPrefix.program.followedBy FixedWidthColumnFrame.program).followedBy
  CiphertextSecondReturn.program

theorem runs_valid (n : Nat) (modulus scalar generator publicKey message first shared second : List Bool)
    (hModulus : modulus.length = n+3)
    (hScalar : scalar.length = modulus.length) (hGenerator : generator.length = modulus.length)
    (hKey : publicKey.length = modulus.length) (hMessage : message.length = modulus.length)
    (hFirst : first.length = modulus.length) (hShared : shared.length = modulus.length)
    (hSecond : second.length = modulus.length) :
    let instanceBits := modulus++scalar++generator++publicKey++message
    let raw := encodeSecurityParameter n ++ frame instanceBits ++ first ++ shared ++ second
    ∃ target used, used ≤ 2000*(n+3)+1000 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.outputBits = frame first ++ frame second := by
  dsimp only
  let instanceBits := modulus++scalar++generator++publicKey++message
  let before := instanceBits.reverse.map some ++
    some false::List.replicate instanceBits.length (some true) ++ some false::List.replicate n (some true)
  let tracks := modulus.map (fun bit => ((false,false),bit))
  let template := BinaryThirdColumnTemplate.columns modulus
  have tracksLength : tracks.length = modulus.length := by simp [tracks]
  have templateEq : BinaryModularAddition.interleave tracks = template := rfl
  have templateLength : template.length = 3*modulus.length := BinaryThirdColumnTemplate.columns_length _
  have firstNonempty : first ≠ [] := by
    intro empty
    have len : first.length = 0 := by rw [empty]; rfl
    rw [hFirst,hModulus] at len
    omega
  have secondNonempty : second ≠ [] := by
    intro empty
    have len : second.length = 0 := by rw [empty]; rfl
    rw [hSecond,hModulus] at len
    omega
  have beforeNonempty : before ≠ [] := by simp [before]
  obtain ⟨located,a,ha,prefixRun,prefixHalt,prefixInput,prefixOutput⟩ :=
    CiphertextReturnPrefix.runs_valid n modulus scalar generator publicKey message first shared second
      hModulus hScalar hGenerator hKey hMessage
  cases shared with
  | nil => simp at hShared; omega
  | cons bit rest =>
    cases beforeEq : before with
    | nil => exact False.elim (beforeNonempty beforeEq)
    | cons previous saved =>
      let tail := rest.map some ++ second.map some ++ [none]
      obtain ⟨framed,b,hb,framing,frameHalt,frameInput,frameOutput⟩ :=
        FixedWidthColumnFrame.runs previous saved (some bit) tail first tracks
          (hFirst.trans tracksLength.symm) firstNonempty
      have sourceEq : atCells (previous::saved) (first.map some++some bit::tail) =
          atCells before ((first++(bit::rest)++second).map some++[none]) := by
        simp [tail,beforeEq,List.map_append,List.append_assoc]
      have frameEntry : ({inputTape := atCells (previous::saved) (first.map some++some bit::tail),outputTape := Tape.ofBits (BinaryModularAddition.interleave tracks)} : Configuration).Equivalent
          (located.resumeAt 0) := by
        refine ⟨rfl,rfl,?_,?_⟩
        · rw [sourceEq]
          exact (padded_bits before (first++(bit::rest)++second)).trans prefixInput.symm
        · exact prefixOutput.symm
      obtain ⟨one,t,ht,r1,h1,i1,o1⟩ := prefixRun.followedBy_equivalent framing frameEntry (Nat.zero_le _) rfl prefixHalt frameHalt
      let field : List (Option Bool) := none::rest.map some
      let secondBefore := first.reverse.map some ++ none::saved
      have fieldLength : field.length = first.length := by
        simp only [field,List.length_cons,List.length_map]
        simp only [List.length_cons] at hShared
        omega
      obtain ⟨returned,c,hc,returnRun,returnHalt,bits⟩ := CiphertextSecondReturn.runs secondBefore field first second
        fieldLength (hSecond.trans hFirst.symm) firstNonempty secondNonempty
      have returnEntry : ({inputTape := atCells secondBefore (field++second.map some++[none]),outputTape := {left := (frame first).reverse.map some}} : Configuration).Equivalent
          (one.resumeAt 0) := by
        refine ⟨rfl,rfl,?_,frameOutput.symm.trans o1⟩
        have source : atCells secondBefore (field++second.map some++[none]) =
            ({left := first.reverse.map some ++ none::saved,right := tail} : Tape) := by
          simp [secondBefore,field,tail,atCells,Tape.moveRight,List.append_assoc]
        rw [source]
        exact frameInput.symm.trans i1
      obtain ⟨target,used,bound,run,halt,_,out⟩ := r1.followedBy_equivalent returnRun returnEntry (Nat.zero_le _) rfl h1 returnHalt
      refine ⟨target,used,?_,run,halt,out.bits.symm.trans bits⟩
      rw [templateEq,templateLength,hFirst,hModulus] at hb
      rw [hFirst,hModulus] at hc
      omega


theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  unfold program
  exact (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ CiphertextReturnPrefix.no_randomBit FixedWidthColumnFrame.no_randomBit) CiphertextSecondReturn.no_randomBit) tape

end Machine.NativeCiphertextReturn
