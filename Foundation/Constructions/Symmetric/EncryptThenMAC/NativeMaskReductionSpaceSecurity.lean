import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskReductionSecurity
import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskReductionSpaceBackend

/-! Security transfer using the operational reduction class whose witnesses
simultaneously certify time, exactly one query at completion, and polynomial
whole-prefix encoded space. Security of a concrete stretching generator
remains an explicit cryptographic assumption. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativeMaskReductionSpaceSecurity
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC Foundation.Examples
open CryptoLogic.General
open ReusableBlockPad.NativeObserver (publicCaller observer)
open scoped ENNReal
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {G : Generator} (I : GeneratedBlockMask.PRG.Implementation.{v} G)
    (samples : ∀ n, I.Input n) {State : Type u} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (messages : ∀ n, G.Messages n)
    {Output : Type w} (Q : Machine.Procedure Machine.Configuration Output)
    (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (observerCap : Nat → Nat)
    (hCap : ∀ n ciphertext, ciphertext.length = G.outputLength n →
      Q.execution.budget (publicCaller ciphertext) ≤ observerCap n)
    (hWidth : PolynomiallyBounded G.outputLength) (hObserver : PolynomiallyBounded observerCap)

include hEntry hHalt hCap hWidth hObserver in
/-- The quantitative loss uses advantages of actual reductions with all
three resource certificates, keeping the same finite observer program. -/
theorem advantage_le (n leftTime rightTime : Nat)
    (hLeft : (I.execution n).budget (samples n) + 50 * G.outputLength n + 40 + observerCap n ≤ leftTime)
    (hRight : (I.execution n).budget (samples n) + 50 * G.outputLength n + 40 + observerCap n ≤ rightTime) :
    probabilityGap
      (eventProb (GeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).1 (samples n) Q leftTime) (· = true))
      (eventProb (GeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).2 (samples n) Q rightTime) (· = true)) ≤
    (NativeMaskReductionSpaceBackend.registration G).nativeAdvantage messages Q.code
      (NativeMaskReductionSpaceBackend.witness G Q false observerCap messages hWidth hObserver hEntry hHalt hCap).resources n +
    (NativeMaskReductionSpaceBackend.registration G).nativeAdvantage messages Q.code
      (NativeMaskReductionSpaceBackend.witness G Q true observerCap messages hWidth hObserver hEntry hHalt hCap).resources n := by
  exact NativeMaskReductionSecurity.advantage_le I samples oracle state trace messages Q hEntry hHalt
    observerCap hCap hWidth hObserver n leftTime rightTime hLeft hRight

include hEntry hHalt hCap hWidth hObserver in
/-- The generated encryption experiment has polynomial time and negligible
advantage. Its two reductions additionally have polynomial whole-prefix space,
with concrete membership proved rather than assumed. -/
theorem security_time_and_reduction_space
    (hGeneration : PolynomiallyBounded (fun n => (I.execution n).budget (samples n)))
    (hSecure : (NativeMaskReductionSpaceBackend.registration G).object.Secure messages) :
    PolynomiallyBounded (NativeMaskReductionSecurity.horizon I samples observerCap) ∧
    PolynomiallyBounded (NativeMaskReductionSpaceBackend.bitCap G Q.code observerCap) ∧
    Negligible (fun n => probabilityGap
      (eventProb (GeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).1 (samples n) Q
        (NativeMaskReductionSecurity.horizon I samples observerCap n)) (· = true))
      (eventProb (GeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).2 (samples n) Q
        (NativeMaskReductionSecurity.horizon I samples observerCap n)) (· = true))) := by
  refine ⟨GeneratedBlockMask.PRG.NativeObserver.Implementation.time_polynomial I samples hGeneration hWidth hObserver,
    NativeMaskReductionSpaceBackend.bitCap_polynomial G Q.code observerCap hWidth hObserver, ?_⟩
  have hLeft := hSecure (NativeMaskReductionBackend.adversary G Q false messages)
    (NativeMaskReductionSpaceBackend.witness G Q false observerCap messages hWidth hObserver hEntry hHalt hCap).admissible
  have hRight := hSecure (NativeMaskReductionBackend.adversary G Q true messages)
    (NativeMaskReductionSpaceBackend.witness G Q true observerCap messages hWidth hObserver hEntry hHalt hCap).admissible
  exact GeneratedBlockMask.PRG.NativeObserver.Implementation.negligible I samples oracle state trace messages
    Q hEntry hHalt observerCap (NativeMaskReductionSecurity.horizon I samples observerCap)
    hCap (fun _ => Nat.le_refl _) hLeft hRight

end Foundation.Symmetric.EncryptThenMAC.NativeMaskReductionSpaceSecurity
