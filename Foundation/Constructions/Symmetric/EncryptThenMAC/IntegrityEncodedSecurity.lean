import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityEncodedBackend
import Foundation.Crypto.Logic.General.ExecutionRefinement
import Foundation.Crypto.Meta.General.ResourceSecurity

/-! The integrity reduction maps polynomial-input witnesses to actual
whole-code/state bit certificates, retaining its cryptographic loss. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
open Machine Foundation.Probability CryptoOracle CryptoLogic.General
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def inputCertificate (width : Nat → Nat) : (sourceObject width).Certificate :=
  fun _ _ r => PolynomiallyBounded (fun n => (r.input n).length)

def encodedCertificate (width : Nat → Nat) : (targetObject width).Certificate :=
  fun _ code r => ∃ bits : Nat → Nat, PolynomiallyBounded bits ∧
    ∀ n (macKey : TableMAC.Key (width n)) elapsed, elapsed ≤ IntegrityMachine.executionBudget (width n) (r.count n) →
      ∀ target ∈ (IntegrityMachine.eval code.source (IntegrityGameCodec.byteSigningOracle macKey)
        elapsed (IntegrityMachine.initial () (r.input n))).support,
        ((IntegrityEncoding.complete FiniteBitEncoding.unit).encode
          (IntegrityEncoding.nativePrograms, code.source, target)).length ≤ bits n

noncomputable def inputObject (width : Nat → Nat) := (sourceObject width).refine (inputCertificate width)
noncomputable def encodedObject (width : Nat → Nat) := (targetObject width).refine (encodedCertificate width)

noncomputable def encodedReduction (width : Nat → Nat) :
    CertifiedReduction (inputObject width) (encodedObject width) :=
  (certifiedReduction width).refine (inputCertificate width) (encodedCertificate width) (by
    intro F A W hInput
    refine ⟨(fun n => encodedBudget W.code (width n) (W.resources.input n).length (W.resources.count n)),
      certificate_encoded_polynomial width F A W hInput, ?_⟩
    intro n key elapsed hElapsed target hTarget
    exact certificate_encoded_peak width F A W n key elapsed hElapsed target hTarget)

@[simp] theorem encodedReduction_compiler (width : Nat → Nat) :
    (encodedReduction width).compiler = compiler := rfl

@[simp] theorem encodedReduction_loss (width : Nat → Nat) :
    (encodedReduction width).reduction.loss = (reduction width).loss := rfl

theorem encoded_secure (width : Nat → Nat) (F : InstanceFamily (integrityGoal width))
    (h : (encodedObject width).Secure ((reduction width).mapFamily F)) :
    (inputObject width).Secure F :=
  (encodedReduction width).secure F h

theorem encoded_bound (width : Nat → Nat) (F : InstanceFamily (integrityGoal width))
    (epsilon : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin (encodedObject width).goal (encodedObject width).adversaries
      ((reduction width).mapFamily F) epsilon) :
    BoundedByOnWithin (inputObject width).goal (inputObject width).adversaries F epsilon :=
  (encodedReduction width).bounded F epsilon h

end Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
