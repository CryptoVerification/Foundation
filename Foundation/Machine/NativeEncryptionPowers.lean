import Foundation.Machine.NativeEncryptionFirstPower
import Foundation.Machine.NativeEncryptionSharedPower

namespace Machine.NativeEncryptionPowers

/-- Both native powers use the very same sampled scalar. Their results
are retained together with the original key and message for multiplication. -/
def program : Program := NativeEncryptionFirstPower.program.followedBy
  NativeEncryptionSharedPower.program

theorem runs_numbers (n modulus order generator scalar publicKey message : Nat)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hOrder : order < 2^(n+3)) (hScalar : scalar < 2^(n+3))
    (hGenerator : generator < modulus) (hKey : publicKey < modulus) :
    let p := Binary.encode (n+3) modulus
    let q := Binary.encode (n+3) order
    let g := Binary.encode (n+3) generator
    let s := Binary.encode (n+3) scalar
    let h := Binary.encode (n+3) publicKey
    let m := Binary.encode (n+3) message
    let raw := encodeSecurityParameter n ++ frame (p++q++g++h++m)
    let modified := encodeSecurityParameter n ++ frame (p++s++g++h++m)
    ∃ target used, used ≤ 2*NativeKeygenContinuation.budget n+1 ∧
      RunsFor program
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some},
          outputTape := {left := s.reverse.map some}} : Configuration) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits (modified ++
        Binary.encode (n+3) (generator^scalar % modulus) ++
        Binary.encode (n+3) (publicKey^scalar % modulus))) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  obtain ⟨first,u,hu,firstRun,firstHalt,firstInput,firstOutput⟩ :=
    NativeEncryptionFirstPower.runs_numbers n modulus order generator scalar publicKey message
      hOne hModulus hOrder hScalar hGenerator
  obtain ⟨second,v,hv,secondRun,secondHalt,secondInput,secondOutput⟩ :=
    NativeEncryptionSharedPower.runs_numbers n modulus scalar generator publicKey message
      (Binary.encode (n+3) (generator^scalar % modulus)) (by simp)
      hOne hModulus hScalar hKey
  have boundary : (Configuration.initial (encodeSecurityParameter n ++ frame
      (Binary.encode (n+3) modulus ++ Binary.encode (n+3) scalar ++
        Binary.encode (n+3) generator ++ Binary.encode (n+3) publicKey ++
        Binary.encode (n+3) message) ++ Binary.encode (n+3) (generator^scalar % modulus))).Equivalent
        (first.resumeAt 0) := by
    refine ⟨rfl,rfl,?_,firstOutput.symm⟩
    simpa only [List.append_assoc,Configuration.initial,Configuration.resumeAt] using firstInput.symm
  obtain ⟨target,used,bound,run,halt,input,output⟩ :=
    firstRun.followedBy_equivalent secondRun boundary (Nat.zero_le _) rfl firstHalt secondHalt
  refine ⟨target,used,by omega,?_,halt,?_,output.symm.trans secondOutput⟩
  · simpa only [program,List.append_assoc] using run
  · exact input.symm.trans secondInput

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ NativeEncryptionFirstPower.no_randomBit
    NativeEncryptionSharedPower.no_randomBit tape

end Machine.NativeEncryptionPowers
