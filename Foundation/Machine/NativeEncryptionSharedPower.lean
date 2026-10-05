import Foundation.Machine.FramedSharedPower
import Foundation.Machine.ReturnJoinedPower
import Foundation.Machine.NativeKeygenContinuation

namespace Machine.NativeEncryptionSharedPower

/-- Use the exponent already retained by the first power. The public key
is read from the same request, and the first ciphertext component is kept
while the actual shared group element is appended to the input. -/
def program : Program := FramedSharedPower.program.followedBy ReturnJoinedPower.program

theorem runs_numbers (n modulus scalar generator publicKey message : Nat)
    (firstComponent : List Bool) (hFirst : firstComponent.length = n+3)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hScalar : scalar < 2^(n+3)) (hKey : publicKey < modulus) :
    let p := Binary.encode (n+3) modulus
    let s := Binary.encode (n+3) scalar
    let g := Binary.encode (n+3) generator
    let h := Binary.encode (n+3) publicKey
    let m := Binary.encode (n+3) message
    let raw := encodeSecurityParameter n ++ frame (p++s++g++h++m) ++ firstComponent
    ∃ target used, used ≤ NativeKeygenContinuation.budget n ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent
        (Tape.ofBits (raw ++ Binary.encode (n+3) (publicKey^scalar % modulus))) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let p := Binary.encode (n+3) modulus
  let s := Binary.encode (n+3) scalar
  let g := Binary.encode (n+3) generator
  let h := Binary.encode (n+3) publicKey
  let m := Binary.encode (n+3) message
  let raw := encodeSecurityParameter n ++ frame (p++s++g++h++m) ++ firstComponent
  let columns := BinaryColumnSlotFill.fullSlots h s p
  obtain ⟨c, powered, u, hu, powerRun, powerHalt, _, coreBits, powerInput, powerOutput⟩ :=
    FramedSharedPower.runs_numbers n modulus scalar generator publicKey message firstComponent
      hOne hModulus hScalar hKey
  have columnsLength : columns.length = 3*(n+3) := by
    simp [columns, BinaryColumnSlotFill.fullSlots_length, p,s,h]
  have rawLength : raw.length = n+11*(n+3)+2 := by
    simp [raw,p,s,g,h,m,frame,encodeSecurityParameter,hFirst]; omega
  have powerLength : c.outputBits.length = n+3 := by rw [coreBits]; simp
  have hPowerBudget : u ≤ NativeKeygenContinuation.powerBudget n := by
    have validLength : FramedExponentPreparation.validBudget n p s (g++h++m) ≤ 300*(n+3) := by
      simp [FramedExponentPreparation.validBudget, BinaryThirdColumnTemplate.columns_length, p,s,g,h,m]
      omega
    change u ≤ FramedExponentPreparation.validBudget n p s (g++h++m)+8*columns.length+
      6*g.length+9*h.length+3*(m++firstComponent).length+61+
        GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length at hu
    rw [columnsLength] at hu
    have gLength : g.length = n+3 := by simp [g]
    have keyLength : h.length = n+3 := by simp [h]
    have restLength : (m++firstComponent).length = 2*(n+3) := by simp [m,hFirst]; omega
    rw [gLength,keyLength,restLength] at hu
    unfold NativeKeygenContinuation.powerBudget
    omega
  obtain ⟨joined, v, hv, joinRun, joinHalt, joinInput, joinOutput⟩ :=
    ReturnJoinedPower.runs BinaryPowerExternalWidth.program columns raw c
  have boundary : ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
      (none::raw.reverse.map some) c).swapTapes.resumeAt 0).Equivalent (powered.resumeAt 0) :=
    ⟨rfl, rfl, powerInput.symm, powerOutput.symm⟩
  obtain ⟨target, used, bound, run, halt, input, output⟩ :=
    powerRun.followedBy_equivalent joinRun boundary (Nat.zero_le _) rfl powerHalt joinHalt
  refine ⟨target, used, ?_, run, halt, ?_, output.symm.trans joinOutput⟩
  · have storage := NativeKeygenReturn.source_cells_le_of_run columns raw c powerRun powerOutput
    have startCells : (Configuration.initial raw).inputTape.cells+(Configuration.initial raw).outputTape.cells ≤ raw.length+2 := by
      cases raw <;> simp [Configuration.initial,Tape.ofBits,Tape.cells] <;> omega
    have storageBound := storage.trans (Nat.add_le_add_right startCells u)
    rw [rawLength] at storageBound
    have returnBudget := ReturnJoinedPower.budget_le columns raw c
    rw [columnsLength,rawLength,powerLength] at returnBudget
    have limit := hv.trans returnBudget
    unfold NativeKeygenContinuation.budget
    omega
  · rw [coreBits] at joinInput
    exact input.symm.trans joinInput

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ FramedSharedPower.no_randomBit ReturnJoinedPower.no_randomBit tape

end Machine.NativeEncryptionSharedPower
