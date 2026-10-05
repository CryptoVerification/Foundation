import Foundation.Crypto.Semantics.Machine.FramedCiphertextProductInput
import Foundation.Crypto.Semantics.Machine.BinaryProductExternalWidth
import Foundation.Crypto.Semantics.Machine.ReturnJoinedPower
import Foundation.Crypto.Semantics.Machine.NativeKeygenReturn

namespace Machine.NativeCiphertextProduct

private def arithmetic : Program := FramedCiphertextProductInput.program.followedBy
  (GuardedCompiler.rawCompileOpposite BinaryProductExternalWidth.program)

/-- The final native multiplication appends its actual result to the
retained request and both powers, then clears the arithmetic scratch tape. -/
def program : Program := arithmetic.followedBy ReturnJoinedPower.program

def arithmeticBudget (n : Nat) : Nat := 1000*(n+3)+1+
  GuardedCompiler.rawTraceBudget BinaryProductExternalWidth.budget (3*(n+3))

def budget (n : Nat) : Nat := 9*arithmeticBudget n+2000*(n+3)

private theorem initial_cells_le (raw : List Bool) :
    (Configuration.initial raw).inputTape.cells +
      (Configuration.initial raw).outputTape.cells ≤ raw.length + 2 := by
  cases raw <;> simp [Configuration.initial, Tape.ofBits, Tape.cells] <;> omega

private theorem blank_boundary (columns : List Bool) :
    ({Tape.ofBits columns with left := [none]} : Tape).Equivalent (Tape.ofBits columns) := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro i
  cases columns <;> cases i <;> rfl

private theorem runs_prepared (source preparation : Program) (sourceBudget : Nat → Nat)
    (raw columns result : List Bool) (prepared : Configuration) (u : Nat)
    (prep : RunsFor preparation (Configuration.initial raw) prepared u)
    (prepHalt : prepared.halted = true)
    (prepInput : prepared.inputTape.Equivalent ({left := none::raw.reverse.map some} : Tape))
    (prepOutput : prepared.outputTape.Equivalent (Tape.ofBits columns))
    (noRandom : ∀ tape, Instruction.randomBit tape ∉ source)
    (stops : HaltsWithin source columns (sourceBudget columns.length))
    (correct : evalWithin source columns (sourceBudget columns.length) = PMF.pure (some result)) :
    ∃ c target used,
      c.outputBits = result ∧
      used ≤ u+GuardedCompiler.rawTraceBudget sourceBudget columns.length+
        ReturnJoinedPower.budget columns raw c+2 ∧
      RunsFor ((preparation.followedBy (GuardedCompiler.rawCompileOpposite source)).followedBy ReturnJoinedPower.program)
        (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits (raw++result)) ∧
      target.outputTape.Equivalent ({} : Tape) ∧
      c.inputTape.cells ≤ raw.length+2+u+GuardedCompiler.rawTraceBudget sourceBudget columns.length+1 := by
  let saved := none::raw.reverse.map some
  obtain ⟨c, _, coreBits, law⟩ := GuardedCompiler.rawCompileOpposite_result
    source columns result [none] saved sourceBudget noRandom stops correct
  let returned := (GuardedCompiler.rawResultFrom source columns [none] saved c).swapTapes
  have trace : PaddedRunsFor (GuardedCompiler.rawCompileOpposite source)
      (GuardedCompiler.packInputStart [none] saved columns).swapTapes returned
      (GuardedCompiler.rawTraceBudget sourceBudget columns.length) := by
    apply (mem_support_evalConfigWithin_iff _ _ _ _).mp
    rw [law]
    simp [returned]
  obtain ⟨vUsed,hv,call⟩ := trace.toRunsFor_le
  have boundary : (GuardedCompiler.packInputStart [none] saved columns).swapTapes.Equivalent
      (prepared.resumeAt 0) :=
    ⟨rfl,rfl,prepInput.symm,(blank_boundary columns).trans prepOutput.symm⟩
  obtain ⟨powered,t,ht,powerRun,powerHalt,powerInput,powerOutput⟩ :=
    prep.followedBy_equivalent call boundary (Nat.zero_le _) rfl prepHalt rfl
  have storage := NativeKeygenReturn.source_cells_le_of_run
    (source := source) columns raw c powerRun powerOutput.symm
  have storageBound := storage.trans (Nat.add_le_add_right (initial_cells_le raw) t)
  obtain ⟨joined,j,hj,joinRun,joinHalt,joinInput,joinOutput⟩ :=
    ReturnJoinedPower.runs source columns raw c
  have joinBoundary : ((GuardedCompiler.rawResultFrom source columns [none] saved c).swapTapes.resumeAt 0).Equivalent
      (powered.resumeAt 0) := ⟨rfl,rfl,powerInput,powerOutput⟩
  obtain ⟨target,used,bound,run,halt,inp,out⟩ :=
    powerRun.followedBy_equivalent joinRun joinBoundary (Nat.zero_le _) rfl powerHalt joinHalt
  refine ⟨c,target,used,coreBits,?_,run,halt,?_,out.symm.trans joinOutput,?_⟩
  · omega
  · rw [coreBits] at joinInput
    exact inp.symm.trans joinInput
  · omega

private theorem total_budget (n trace u used storage returnCost : Nat)
    (hu : u ≤ 1000*(n+3))
    (hs : storage ≤ (n+12*(n+3)+2)+2+u+trace+1)
    (hr : returnCost ≤ 8*storage+4*(3*(n+3))+2*(n+12*(n+3)+2)+40*(n+3)+100)
    (hused : used ≤ u+trace+returnCost+2) :
    used ≤ 9*(1000*(n+3)+1+trace)+2000*(n+3) := by omega

theorem runs_numbers (n modulus scalar generator publicKey message : Nat)
    (firstComponent shared : List Bool) (hFirst : firstComponent.length = n+3)
    (sharedValue : Nat) (hShared : shared = Binary.encode (n+3) sharedValue)
    (hModulus : modulus < 2^(n+3)) (hMessage : message < modulus)
    (hSharedValue : sharedValue < modulus) :
    let p := Binary.encode (n+3) modulus
    let s := Binary.encode (n+3) scalar
    let g := Binary.encode (n+3) generator
    let h := Binary.encode (n+3) publicKey
    let m := Binary.encode (n+3) message
    let raw := encodeSecurityParameter n ++ frame (p++s++g++h++m) ++ firstComponent ++ shared
    ∃ target used, used ≤ budget n ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits (raw ++ Binary.encode (n+3) (message*sharedValue % modulus))) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  subst shared
  let p := Binary.encode (n+3) modulus
  let s := Binary.encode (n+3) scalar
  let g := Binary.encode (n+3) generator
  let h := Binary.encode (n+3) publicKey
  let m := Binary.encode (n+3) message
  let v := Binary.encode (n+3) sharedValue
  let raw := encodeSecurityParameter n ++ frame (p++s++g++h++m) ++ firstComponent ++ v
  let columns := BinaryColumnSlotFill.fullSlots m v p
  obtain ⟨prepared,u,hu,prep,prepHalt,prepInput,prepOutput⟩ :=
    FramedCiphertextProductInput.runs_valid n p s g h m firstComponent v
      (by simp [p]) (by simp [s,p]) (by simp [g,p]) (by simp [h,p])
      (by simp [m,p]) (by simpa [p] using hFirst) (by simp [v,p])
  have correct : evalWithin BinaryProductExternalWidth.program columns
      (BinaryProductExternalWidth.budget columns.length) =
        PMF.pure (some (Binary.encode (n+3) (message*sharedValue % modulus))) := by
    simpa only [columns,m,v,p,BinaryColumnSlotFill.fullSlots,BinaryProductExternalWidth.numberColumns]
      using BinaryProductExternalWidth.eval_numbers (n+3) modulus message sharedValue hMessage hSharedValue hModulus
  obtain ⟨c,target,used,coreBits,bound,run,halt,input,output,storage⟩ :=
    runs_prepared BinaryProductExternalWidth.program FramedCiphertextProductInput.program
      BinaryProductExternalWidth.budget raw columns _ prepared u prep prepHalt prepInput prepOutput
      BinaryProductExternalWidth.no_randomBit (BinaryProductExternalWidth.haltsWithin columns) correct
  have columnsLength : columns.length = 3*(n+3) := by
    simp [columns,BinaryColumnSlotFill.fullSlots_length,m,v,p]
  have rawLength : raw.length = n+12*(n+3)+2 := by
    simp [raw,p,s,g,h,m,v,frame,encodeSecurityParameter,hFirst]; omega
  have outLength : c.outputBits.length = n+3 := by rw [coreBits]; simp
  have returnBound := ReturnJoinedPower.budget_le columns raw c
  rw [columnsLength,rawLength,outLength] at returnBound
  rw [columnsLength,rawLength] at storage
  rw [columnsLength] at bound
  refine ⟨target,used,?_,run,halt,input,output⟩
  exact total_budget n (GuardedCompiler.rawTraceBudget BinaryProductExternalWidth.budget (3*(n+3)))
    u used c.inputTape.cells (ReturnJoinedPower.budget columns raw c) hu storage returnBound bound

theorem budget_polynomiallyBounded : PolynomiallyBounded budget := by
  have width := PolynomiallyBounded.id.add (PolynomiallyBounded.const 3)
  have columns := (PolynomiallyBounded.const 3).mul width
  have source := ((PolynomiallyBounded.const 5).mul columns).add
    (PolynomiallyBounded.const 19)
  have product := (PolynomiallyBounded.const 1000000).mul
    ((columns.add (PolynomiallyBounded.const 4)).pow 4)
  have sourceBound : PolynomiallyBounded (fun n => BinaryProductExternalWidth.budget (3*(n+3))) := by
    simpa [BinaryProductExternalWidth.budget,BinaryProductPadded.budget,
      BinaryWorkspacePreparation.budget,BinaryProductProgram.budget,Nat.add_assoc]
      using (source.add product).add (PolynomiallyBounded.const 5)
  have guarded := ((PolynomiallyBounded.const 125).mul
    (columns.add (PolynomiallyBounded.const 1))).mul
      ((sourceBound.add (PolynomiallyBounded.const 1)).pow 2)
  have actual := guarded.mono (fun n => GuardedCompiler.rawTraceBudget_bound
    BinaryProductExternalWidth.budget (3*(n+3)))
  exact ((PolynomiallyBounded.const 9).mul
    ((((PolynomiallyBounded.const 1000).mul width).add (PolynomiallyBounded.const 1)).add actual)).add
      ((PolynomiallyBounded.const 2000).mul width)


theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  unfold program
  exact (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ FramedCiphertextProductInput.no_randomBit (GuardedCompiler.rawCompileOpposite_no_randomBit _ BinaryProductExternalWidth.no_randomBit)) ReturnJoinedPower.no_randomBit) tape

end Machine.NativeCiphertextProduct
