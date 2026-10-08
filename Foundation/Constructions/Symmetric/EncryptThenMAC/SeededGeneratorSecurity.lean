import Foundation.Constructions.Symmetric.EncryptThenMAC.SeededGeneratorImplementation
import Foundation.Constructions.Symmetric.EncryptThenMAC.ProjectedNativeMaskReductionSpaceSecurity

/-! Seed sampling, native expansion, masking and native observation in one
security theorem. The generator code is the actual linked sampler/expander.
Reduction membership is supplied by existing finite time/query/space
witnesses; pseudorandomness of G remains an explicit cryptographic premise. -/
namespace Foundation.Symmetric.EncryptThenMAC.SeededGeneratorImplementation.Expander
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Examples
open ReusableBlockPad.NativeObserver (publicCaller)
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {G : Generator} (E : Expander.{u} G)

/-- Total budget, including actual uniform seed generation. -/
def encryptionHorizon (observerCap : Nat → Nat) (n : Nat) : Nat :=
  5 * G.seedLength n + E.cap n + 3 + 50 * G.outputLength n + 40 + observerCap n

theorem encryption_time_polynomial (observerCap : Nat → Nat)
    (hSeed : PolynomiallyBounded G.seedLength) (hExpand : PolynomiallyBounded E.cap)
    (hWidth : PolynomiallyBounded G.outputLength) (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (E.encryptionHorizon observerCap) := by
  have h := ProjectedGeneratedBlockMask.PRG.NativeObserver.Implementation.time_polynomial
    E.projected (fun _ => ()) (E.time_polynomial hSeed hExpand) hWidth hObserver
  change PolynomiallyBounded (fun n => 5 * G.seedLength n + E.cap n + 3 + 50 * G.outputLength n + 40 + observerCap n)
  simpa only [projected_budget] using h

/-- The finite implementation and the cryptographic premise meet here.
Neither seed generation nor native expansion is a free logical operation. -/
theorem encryption_security_and_resources
    {State : Type v} (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (messages : ∀ n, G.Messages n) {Output : Type w}
    (Q : Machine.Procedure Configuration Output)
    (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (observerCap : Nat → Nat)
    (hCap : ∀ n ciphertext, ciphertext.length = G.outputLength n →
      Q.execution.budget (publicCaller ciphertext) ≤ observerCap n)
    (hSeed : PolynomiallyBounded G.seedLength) (hExpand : PolynomiallyBounded E.cap)
    (hWidth : PolynomiallyBounded G.outputLength) (hObserver : PolynomiallyBounded observerCap)
    (hSecure : (NativeMaskReductionSpaceBackend.registration G).object.Secure messages) :
    PolynomiallyBounded (E.encryptionHorizon observerCap) ∧
    PolynomiallyBounded (NativeMaskReductionSpaceBackend.bitCap G Q.code observerCap) ∧
    Negligible (fun n => probabilityGap
      (eventProb (ProjectedGeneratedBlockMask.NativeObserver.game (E.projected.native n) oracle state trace
        (messages n).1 () Q (E.encryptionHorizon observerCap n)) (· = true))
      (eventProb (ProjectedGeneratedBlockMask.NativeObserver.game (E.projected.native n) oracle state trace
        (messages n).2 () Q (E.encryptionHorizon observerCap n)) (· = true))) := by
  have h := ProjectedNativeMaskReductionSpaceSecurity.security_time_and_reduction_space
    E.projected (fun _ => ()) oracle state trace messages Q hEntry hHalt observerCap hCap hWidth hObserver
    (E.time_polynomial hSeed hExpand) hSecure
  have he : ProjectedNativeMaskReductionSpaceSecurity.horizon E.projected (fun _ => ()) observerCap =
      E.encryptionHorizon observerCap := by
    funext n
    unfold ProjectedNativeMaskReductionSpaceSecurity.horizon encryptionHorizon
    rw [projected_budget]
  rw [he] at h
  exact h

end Foundation.Symmetric.EncryptThenMAC.SeededGeneratorImplementation.Expander
