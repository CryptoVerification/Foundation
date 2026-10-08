import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskReductionBackend
import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMaskNativeObserverPRG

/-! Use the registered time/query-bounded reduction class in the encryption
security theorem. Membership of both reductions is proved by actual finite
execution witnesses; no membership of arbitrary mathematical observers is
silently postulated. PRG security itself remains a cryptographic premise. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativeMaskReductionSecurity
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
/-- The two terms on the right are advantages of registered, executable,
one-query programs with the same finite observer code. -/
theorem advantage_le (n leftTime rightTime : Nat)
    (hLeft : (I.execution n).budget (samples n) + 50 * G.outputLength n + 40 + observerCap n ≤ leftTime)
    (hRight : (I.execution n).budget (samples n) + 50 * G.outputLength n + 40 + observerCap n ≤ rightTime) :
    probabilityGap
      (eventProb (GeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).1 (samples n) Q leftTime) (· = true))
      (eventProb (GeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).2 (samples n) Q rightTime) (· = true)) ≤
    (NativeMaskReductionBackend.registration G).nativeAdvantage messages Q.code
      (NativeMaskReductionBackend.witness G Q false observerCap messages hEntry hHalt hCap hWidth hObserver).resources n +
    (NativeMaskReductionBackend.registration G).nativeAdvantage messages Q.code
      (NativeMaskReductionBackend.witness G Q true observerCap messages hEntry hHalt hCap hWidth hObserver).resources n := by
  rw [← NativeMaskReductionBackend.witness_code G Q false observerCap messages hEntry hHalt hCap hWidth hObserver,
    NativeMaskReductionBackend.witness_advantage G Q false observerCap messages hEntry hHalt hCap hWidth hObserver n]
  rw [NativeMaskReductionBackend.witness_code]
  rw [← NativeMaskReductionBackend.witness_code G Q true observerCap messages hEntry hHalt hCap hWidth hObserver,
    NativeMaskReductionBackend.witness_advantage G Q true observerCap messages hEntry hHalt hCap hWidth hObserver n]
  exact GeneratedBlockMask.PRG.NativeObserver.advantage_le G n (I.native n) (I.halt n) (I.tape n)
    (I.read n) (I.read_exit n) oracle state trace (samples n) (I.implements n (samples n))
    Q hEntry hHalt (observerCap n) (hCap n) (messages n) leftTime rightTime hLeft hRight

/-- Time of the actual fixed-generator/fixed-observer encryption experiment. -/
def horizon : Nat → Nat := fun n =>
  (I.execution n).budget (samples n) + 50 * G.outputLength n + 40 + observerCap n

include hEntry hHalt hCap hWidth hObserver in
/-- Registered PRG security gives negligible advantage for the actual
whole encryption experiment; its total time is simultaneously polynomial. -/
theorem security_and_time
    (hGeneration : PolynomiallyBounded (fun n => (I.execution n).budget (samples n)))
    (hSecure : (NativeMaskReductionBackend.registration G).object.Secure messages) :
    PolynomiallyBounded (horizon I samples observerCap) ∧
    Negligible (fun n => probabilityGap
      (eventProb (GeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).1 (samples n) Q
        (horizon I samples observerCap n)) (· = true))
      (eventProb (GeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).2 (samples n) Q
        (horizon I samples observerCap n)) (· = true))) := by
  refine ⟨GeneratedBlockMask.PRG.NativeObserver.Implementation.time_polynomial I samples hGeneration hWidth hObserver, ?_⟩
  have hLeft := hSecure (NativeMaskReductionBackend.adversary G Q false messages)
    (NativeMaskReductionBackend.witness G Q false observerCap messages hEntry hHalt hCap hWidth hObserver).admissible
  have hRight := hSecure (NativeMaskReductionBackend.adversary G Q true messages)
    (NativeMaskReductionBackend.witness G Q true observerCap messages hEntry hHalt hCap hWidth hObserver).admissible
  exact GeneratedBlockMask.PRG.NativeObserver.Implementation.negligible I samples oracle state trace messages
    Q hEntry hHalt observerCap (horizon I samples observerCap) hCap (fun _ => Nat.le_refl _) hLeft hRight

end Foundation.Symmetric.EncryptThenMAC.NativeMaskReductionSecurity
