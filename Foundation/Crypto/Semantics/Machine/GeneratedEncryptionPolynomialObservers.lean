import Foundation.Crypto.Semantics.Machine.EncodedPolynomialObserver
import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionPhysical
import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionCode
import Foundation.Crypto.Semantics.Machine.EncodedObserverSecurity

/-! Actual fixed-code polynomial observers of a supplied complete encryption
exit encoding. The input includes code, both tape representations, control,
and actual encryption time. Encoding length and observer time are explicit.
Serialization into this bit input is not a free native preparation stage. -/
namespace Machine.GeneratedBlockEncryption
open Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

/-- Faithful observer input length at the public plaintext width. -/
def polynomialObserverInputBound (width : Nat) : Nat :=
  103 * width + 503 + 4 * (StructuredCodeEncoding.program.encode fixedCode).length

set_option maxRecDepth 100000 in
theorem polynomialObserverInputBound_eq (width : Nat) : polynomialObserverInputBound width = 103 * width + 73827 := by
  unfold polynomialObserverInputBound
  rw [fixedCode_encoding_length]

theorem physical_observer_input_length (ciphertext : List Bool) :
    (TimedConfigurationEncoding.encode link.code (physicalCipherExit ciphertext, 61 * ciphertext.length + 40)).length =
      polynomialObserverInputBound ciphertext.length := by
  rw [TimedConfigurationEncoding.encode_length, StructuredCodeEncoding.complete_length,
    ConfigurationEncoding.configuration_length, ConfigurationEncoding.tape_length, ConfigurationEncoding.tape_length]
  unfold polynomialObserverInputBound
  rw [fixedCode_eq]
  generalize (StructuredCodeEncoding.program.encode link.code).length = codeLength
  simp [physicalCipherExit]
  omega

theorem arrival_observer_input_length {width : Nat} (message : Bits width) (result : Configuration × Nat)
    (hResult : result ∈ (arrival.procedure.execution.costed message.toList).support) :
    (TimedConfigurationEncoding.encode link.code result).length = polynomialObserverInputBound width := by
  rw [arrival_physical_uniform, PMF.mem_support_map_iff] at hResult
  obtain ⟨ciphertext, _, rfl⟩ := hResult
  simpa only [Bits.length_toList] using physical_observer_input_length ciphertext.toList

theorem polynomialObserverInputBound_polynomial : PolynomiallyBounded polynomialObserverInputBound :=
  (((PolynomiallyBounded.const 103).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 503)).add
    (PolynomiallyBounded.const (4 * (StructuredCodeEncoding.program.encode fixedCode).length))

/-- All machine branches halt within this polynomial in the security parameter. -/
theorem polynomial_observer_halts (observer : PolynomialObserver) {width : Nat} (message : Bits width)
    (result : Configuration × Nat) (hResult : result ∈ (arrival.procedure.execution.costed message.toList).support) :
    HaltsWithin observer.code (TimedConfigurationEncoding.encode link.code result)
      (observer.budget (polynomialObserverInputBound width)) :=
  observer.halts_with_input_bound _ _ (le_of_eq (arrival_observer_input_length message result hResult))

theorem polynomial_observer_budget_polynomial (observer : PolynomialObserver) :
    PolynomiallyBounded (fun width => observer.budget (polynomialObserverInputBound width)) :=
  observer.budget_profile_polynomial polynomialObserverInputBound_polynomial

theorem polynomial_observer_storage_polynomial (observer : PolynomialObserver) :
    PolynomiallyBounded (fun width => observer.storageBound (polynomialObserverInputBound width)) :=
  observer.storage_profile_polynomial polynomialObserverInputBound_polynomial

/-- Even the observer's complete output state and its actual time are identically distributed. -/
theorem polynomial_observer_costed_secrecy (observer : PolynomialObserver) {width : Nat} (left right : Bits width) :
    (arrival.procedure.execution.costed left.toList).bind (observer.costedTimed link.code) =
      (arrival.procedure.execution.costed right.toList).bind (observer.costedTimed link.code) :=
  arrival_representation_perfect_secrecy left right _

theorem polynomial_observer_perfect_secrecy (observer : PolynomialObserver) {width : Nat} (left right : Bits width) :
    (arrival.procedure.execution.costed left.toList).bind (observer.observeTimed link.code) =
      (arrival.procedure.execution.costed right.toList).bind (observer.observeTimed link.code) :=
  arrival_representation_perfect_secrecy left right _

/-- The resource certificate gives a common horizon without padding actual observer time. -/
theorem polynomial_observer_costed_horizon (observer : PolynomialObserver) {width : Nat} (message : Bits width)
    (result : Configuration × Nat) (hResult : result ∈ (arrival.procedure.execution.costed message.toList).support) :
    runToBoundary (stepPMF observer.code) Configuration.halted (observer.budget (polynomialObserverInputBound width))
      (Configuration.initial (TimedConfigurationEncoding.encode link.code result)) = observer.costedTimed link.code result :=
  observer.costed_horizon _ _ (observer.budget_mono (le_of_eq (arrival_observer_input_length message result hResult)))

/-- A uniform bound on every branch of the producer/observer distribution. -/
theorem polynomial_observer_result_bound (observer : PolynomialObserver) {width : Nat} (message : Bits width)
    (observed : Configuration × Nat)
    (hObserved : observed ∈ ((arrival.procedure.execution.costed message.toList).bind
      (observer.costedTimed link.code)).support) :
    observed.2 ≤ observer.budget (polynomialObserverInputBound width) := by
  rw [PMF.mem_support_bind_iff] at hObserved
  obtain ⟨result, hResult, hObserved⟩ := hObserved
  exact observer.costed_input_bound _ _
    (le_of_eq (arrival_observer_input_length message result hResult)) observed hObserved

/-- All intermediate observer states satisfy the security-parameter storage bound. -/
theorem polynomial_observer_storage_peak (observer : PolynomialObserver) {width : Nat} (message : Bits width)
    (result : Configuration × Nat) (hResult : result ∈ (arrival.procedure.execution.costed message.toList).support)
    (elapsed : Nat) (hElapsed : elapsed ≤ observer.budget (polynomialObserverInputBound width))
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF observer.code) elapsed
      (Configuration.initial (TimedConfigurationEncoding.encode link.code result))).support) :
    (StructuredCodeEncoding.completeEncoding.encode (observer.code, state)).length ≤
      observer.storageBound (polynomialObserverInputBound width) := by
  have hLength := arrival_observer_input_length message result hResult
  have h := observer.storage_peak (TimedConfigurationEncoding.encode link.code result) elapsed
    (by rw [hLength]; exact hElapsed) state hState
  simpa only [hLength] using h

/-- A concrete zero-advantage bound for the entire encoded polynomial observer class. -/
theorem encoded_polynomial_observer_bound_zero {width : Nat} (left right : Bits width) :
    ObserverBound (PolynomialObserver.encodedClass (TimedConfigurationEncoding.resultEncoding link.code))
      (arrival.procedure.execution.costed left.toList) (arrival.procedure.execution.costed right.toList) 0 := by
  apply PolynomialObserver.encoded_bound_zero_of_eq
  rw [arrival_physical_uniform, arrival_physical_uniform]

end Machine.GeneratedBlockEncryption
