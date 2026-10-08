import Foundation.Constructions.Symmetric.PRGControlStorage
import Foundation.Crypto.Semantics.Machine.MaskingStorage

/-! Complete encoded-state bounds for both emitted PRG reduction programs,
including header copying, XOR masking, tape loading and native attack code.
The original operational realization and query proofs remain unchanged. -/
namespace Foundation.Symmetric.Generator
open Foundation.Probability Machine CryptoLogic
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A)

def emittedStorageBound (side : Bool) (n : Nat) : Nat :=
  Masking.storageBound (Masking.compile side W.program) 0 (n + 6 * G.outputLength n + 5)
    (G.reductionTime time n)

theorem emitted_initial_retained (side : Bool) (n : Nat) (challenge : Bits (G.outputLength n)) :
    (Masking.initial (Masking.compile side W.program) (G.header n (F n))
      (F n).1.toList (F n).2.toList challenge.toList).retained = n + 6 * G.outputLength n + 5 := by
  cases side <;> simp [Masking.initial, Masking.compile, Masking.Configuration.retained, G.header_length] <;> omega

theorem emitted_encoded_peak (side : Bool) (n : Nat) (challenge : Bits (G.outputLength n))
    (elapsed : Nat) (hElapsed : elapsed ≤ G.reductionTime time n) (target : Masking.Configuration)
    (hTarget : target ∈ (Masking.eval (Masking.compile side W.program)
      (Masking.initial (Masking.compile side W.program) (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList) elapsed).support) :
    (Masking.codeEncoding.encode (Masking.compile side W.program)).length +
      (Masking.configurationEncoding.encode target).length ≤ G.emittedStorageBound time F A W side n := by
  have hp := Masking.encoded_peak (Masking.compile side W.program) (G.reductionTime time n) elapsed hElapsed
    (Masking.initial (Masking.compile side W.program) (G.header n (F n))
      (F n).1.toList (F n).2.toList challenge.toList) target hTarget
  rw [G.emitted_initial_retained time F A W side n challenge] at hp
  exact hp

theorem emittedStorageBound_polynomial (side : Bool)
    (hLength : PolynomiallyBounded G.outputLength) (hTime : PolynomiallyBounded time) :
    PolynomiallyBounded (G.emittedStorageBound time F A W side) :=
  Masking.storageBound_polynomial (Masking.compile side W.program) (PolynomiallyBounded.const 0)
    ((PolynomiallyBounded.id.add ((PolynomiallyBounded.const 6).mul hLength)).add (PolynomiallyBounded.const 5))
    (G.reductionTime_polynomial hTime hLength)

/-- A strengthened target witness carries the original real execution and
game law together with a polynomial bound on every encoded state prefix. -/
structure EncodedChallengeWitness (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.prgGoal) (A : AdversaryFamily G.prgGoal F) where
  operational : G.ChallengeWitness time F A
  bits : Nat → Nat
  polynomial : PolynomiallyBounded bits
  peak : ∀ n (challenge : Bits (G.outputLength n)) elapsed, elapsed ≤ time n →
    ∀ target ∈ (Masking.eval operational.code
      (Masking.initial operational.code (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList) elapsed).support,
      (Masking.codeEncoding.encode operational.code).length +
        (Masking.configurationEncoding.encode target).length ≤ bits n

def mapEncodedWitness (side : Bool) (hLength : PolynomiallyBounded G.outputLength)
    (hTime : PolynomiallyBounded time) :
    G.EncodedChallengeWitness (G.reductionTime time) F (fun n => G.reduce (F n) side (A n)) where
  operational := G.mapWitness time side F A W
  bits := G.emittedStorageBound time F A W side
  polynomial := G.emittedStorageBound_polynomial time F A W side hLength hTime
  peak := G.emitted_encoded_peak time F A W side

theorem mapEncodedWitness_code (side : Bool) (hLength : PolynomiallyBounded G.outputLength)
    (hTime : PolynomiallyBounded time) :
    (G.mapEncodedWitness time F A W side hLength hTime).operational.code = Masking.compile side W.program := rfl

def encodedChallengeClass (G : Generator) (time : Nat → Nat) : AdversaryClass G.prgGoal where
  admissible F A := Nonempty (G.EncodedChallengeWitness time F A)

/-- The same two-branch loss holds when target security is assumed only for
the strengthened class with proved polynomial encoded-state bounds. -/
theorem encoded_resource_secure (G : Generator) (time : Nat → Nat)
    (hLength : PolynomiallyBounded G.outputLength) (hTime : PolynomiallyBounded time)
    (F : InstanceFamily G.encryptionGoal) (epsilon : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin G.prgGoal (G.encodedChallengeClass (G.reductionTime time)) F epsilon) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass time) F (fun n => 2 * epsilon n) := by
  intro A ⟨W⟩ n
  have hl := h (fun n => G.reduce (F n) false (A n))
    ⟨G.mapEncodedWitness time F A W false hLength hTime⟩ n
  have hr := h (fun n => G.reduce (F n) true (A n))
    ⟨G.mapEncodedWitness time F A W true hLength hTime⟩ n
  exact (G.advantage_le n (F n) (A n)).trans
    (by simpa [two_mul, advantageProfile] using add_le_add hl hr)

theorem encoded_resource_secure_asymptotic (G : Generator) (time : Nat → Nat)
    (hLength : PolynomiallyBounded G.outputLength) (hTime : PolynomiallyBounded time)
    (F : InstanceFamily G.encryptionGoal)
    (h : SecureOnWithin G.prgGoal (G.encodedChallengeClass (G.reductionTime time)) F) :
    SecureOnWithin G.encryptionGoal (G.nativeClass time) F := by
  intro A ⟨W⟩
  have hl := h (fun n => G.reduce (F n) false (A n))
    ⟨G.mapEncodedWitness time F A W false hLength hTime⟩
  have hr := h (fun n => G.reduce (F n) true (A n))
    ⟨G.mapEncodedWitness time F A W true hLength hTime⟩
  exact Negligible.mono (fun n => G.advantage_le n (F n) (A n)) (hl.add hr)

end Foundation.Symmetric.Generator
