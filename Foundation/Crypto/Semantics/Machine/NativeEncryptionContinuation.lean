import Foundation.Crypto.Semantics.Machine.NativeEncryptionPowers
import Foundation.Crypto.Semantics.Machine.NativeCiphertextProduct
import Foundation.Crypto.Semantics.Machine.NativeCiphertextReturn

namespace Machine.NativeEncryptionContinuation

/-- Deterministic native continuation of one accepted scalar sample.
The same retained scalar is used for both powers, and the actual product
is returned with the actual first power. Every stage passes its physical
tapes to the next stage. -/
def program : Program := (NativeEncryptionPowers.program.followedBy NativeCiphertextProduct.program).followedBy
  NativeCiphertextReturn.program

def budget (n : Nat) : Nat := 2*NativeKeygenContinuation.budget n+1+
  NativeCiphertextProduct.budget n+1+2000*(n+3)+1000+1

theorem runs_numbers (n modulus order generator scalar publicKey message : Nat)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hOrder : order < 2^(n+3)) (hScalar : scalar < 2^(n+3))
    (hGenerator : generator < modulus) (hKey : publicKey < modulus)
    (hMessage : message < modulus) :
    let p := Binary.encode (n+3) modulus
    let q := Binary.encode (n+3) order
    let g := Binary.encode (n+3) generator
    let s := Binary.encode (n+3) scalar
    let h := Binary.encode (n+3) publicKey
    let m := Binary.encode (n+3) message
    let raw := encodeSecurityParameter n ++ frame (p++q++g++h++m)
    ∃ target used, used ≤ budget n ∧
      RunsFor program
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some},outputTape := {left := s.reverse.map some}} : Configuration)
        target used ∧ target.halted = true ∧
      target.outputBits = frame (Binary.encode (n+3) (generator^scalar % modulus)) ++
        frame (Binary.encode (n+3) (message*(publicKey^scalar % modulus) % modulus)) := by
  dsimp only
  let p := Binary.encode (n+3) modulus
  let s := Binary.encode (n+3) scalar
  let g := Binary.encode (n+3) generator
  let h := Binary.encode (n+3) publicKey
  let m := Binary.encode (n+3) message
  let modified := encodeSecurityParameter n ++ frame (p++s++g++h++m)
  let firstBits := Binary.encode (n+3) (generator^scalar % modulus)
  let sharedBits := Binary.encode (n+3) (publicKey^scalar % modulus)
  let secondBits := Binary.encode (n+3) (message*(publicKey^scalar % modulus) % modulus)
  obtain ⟨powers,a,ha,powersRun,powersHalt,powersInput,powersOutput⟩ :=
    NativeEncryptionPowers.runs_numbers n modulus order generator scalar publicKey message
      hOne hModulus hOrder hScalar hGenerator hKey
  obtain ⟨product,b,hb,productRun,productHalt,productInput,productOutput⟩ :=
    NativeCiphertextProduct.runs_numbers n modulus scalar generator publicKey message firstBits sharedBits
      (by simp [firstBits]) (publicKey^scalar % modulus) rfl hModulus hMessage
      (Nat.mod_lt _ (by omega))
  have productEntry : (Configuration.initial (modified++firstBits++sharedBits)).Equivalent (powers.resumeAt 0) :=
    ⟨rfl,rfl,powersInput.symm,powersOutput.symm⟩
  obtain ⟨middle,t,ht,middleRun,middleHalt,middleInput,middleOutput⟩ :=
    powersRun.followedBy_equivalent productRun productEntry (Nat.zero_le _) rfl powersHalt productHalt
  obtain ⟨returned,c,hc,returnRun,returnHalt,bits⟩ := NativeCiphertextReturn.runs_valid n p s g h m firstBits sharedBits secondBits
    (by simp [p]) (by simp [s,p]) (by simp [g,p]) (by simp [h,p]) (by simp [m,p])
    (by simp [firstBits,p]) (by simp [sharedBits,p]) (by simp [secondBits,p])
  have returnEntry : (Configuration.initial (modified++firstBits++sharedBits++secondBits)).Equivalent (middle.resumeAt 0) :=
    ⟨rfl,rfl,productInput.symm.trans middleInput,productOutput.symm.trans middleOutput⟩
  obtain ⟨target,used,bound,run,halt,_,out⟩ :=
    middleRun.followedBy_equivalent returnRun returnEntry (Nat.zero_le _) rfl middleHalt returnHalt
  refine ⟨target,used,?_,?_,halt,out.bits.symm.trans bits⟩
  · unfold budget
    omega
  · simpa only [program,List.append_assoc] using run

theorem budget_polynomiallyBounded : PolynomiallyBounded budget :=
  ((((((PolynomiallyBounded.const 2).mul NativeKeygenContinuation.budget_polynomiallyBounded).add
    (PolynomiallyBounded.const 1)).add NativeCiphertextProduct.budget_polynomiallyBounded).add
    (PolynomiallyBounded.const 1)).add
      ((PolynomiallyBounded.const 2000).mul (PolynomiallyBounded.id.add (PolynomiallyBounded.const 3)))).add
      (PolynomiallyBounded.const 1000) |>.add (PolynomiallyBounded.const 1)

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _
    (Program.followedBy_no_randomBit _ _ NativeEncryptionPowers.no_randomBit NativeCiphertextProduct.no_randomBit)
    NativeCiphertextReturn.no_randomBit tape

end Machine.NativeEncryptionContinuation
