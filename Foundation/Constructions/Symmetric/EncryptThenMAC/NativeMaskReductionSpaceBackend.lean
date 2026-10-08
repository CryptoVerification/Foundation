import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskReductionBackend
import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskChallengeWholeResources
import Foundation.Crypto.Logic.General.CertifiedObservedExecution

/-! Register the same operational reductions with time, event-count and whole
encoded-space certificates simultaneously. The original faithful-context
condition remains in force, so resource profiles cannot change the challenge
law or supply hidden advice. No code or game is changed by certification. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativeMaskReductionSpaceBackend
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC Foundation.Examples
open CryptoLogic.General ContractObservedBackend
open ReusableBlockPad.NativeObserver (publicCaller observer)
universe u
set_option backward.isDefEq.respectTransparency false

/-- Counts all finite runtime codes, original caller data and the complete
current outer-controller state, including the saved observer producer. -/
def measure (code : Program) (context : NativeMaskReductionBackend.Context)
    (target : NativeMaskChallenge.Control) : Nat :=
  ((NativeMaskChallenge.WholeResources.completeEncoding context.message).encode
    (Machine.OneTimePad.keygen, PrivateKeyCopy.code, FlaggedBlockXor.code, ReusableBlockPad.code,
      NativeMaskChallenge.loadCode, code, NativeMaskChallenge.WholeResources.caller context.message, target)).length

noncomputable def registration (G : Generator) :=
  (NativeMaskReductionBackend.registration G).certify (Nat → Nat)
    (fun F code resources cap => resources.1.WithinPeak NativeMaskReductionBackend.runtime measure cap F code)

def bitCap (G : Generator) (code : Program) (observerCap : Nat → Nat) (n : Nat) :=
  NativeMaskChallenge.WholeResources.bitBound code (G.outputLength n)
    (52 * G.outputLength n + 42 + observerCap n)

theorem bitCap_polynomial (G : Generator) (code : Program) (observerCap : Nat → Nat)
    (hWidth : PolynomiallyBounded G.outputLength) (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (bitCap G code observerCap) :=
  NativeMaskChallenge.WholeResources.bitBound_polynomial code hWidth
    (NativeMaskChallenge.time_polynomial hWidth hObserver)

variable (G : Generator) {Output : Type u} (Q : Machine.Procedure Machine.Configuration Output)
    (branch : Bool) (observerCap : Nat → Nat) (F : InstanceFamily G.prgGoal)
    (hWidth : PolynomiallyBounded G.outputLength) (hObserver : PolynomiallyBounded observerCap)

include hWidth hObserver in
/-- Whole-prefix space is proved independently of halting and PRG security. -/
theorem peak : (NativeMaskReductionBackend.profile G Q branch observerCap).WithinPeak
    NativeMaskReductionBackend.runtime measure (bitCap G Q.code observerCap) F Q.code := by
  refine ⟨NativeMaskChallenge.WholeResources.bitBound_polynomial Q.code hWidth
    (NativeMaskChallenge.time_polynomial hWidth hObserver), ?_⟩
  intro n world elapsed he target ht
  exact NativeMaskChallenge.WholeResources.peak (G.message (F n) branch)
    (if world then G.ideal n else G.real n) Q.code
    (52 * G.outputLength n + 42 + observerCap n) elapsed he target ht

variable (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (hCap : ∀ n ciphertext, ciphertext.length = G.outputLength n →
      Q.execution.budget (publicCaller ciphertext) ≤ observerCap n)

include hWidth hObserver hEntry hHalt hCap in
/-- Both reduction branches have actual finite-code witnesses satisfying all
three resource bounds and the original faithful environment restriction. -/
noncomputable def witness :
    (registration G).object.Witness F (NativeMaskReductionBackend.adversary G Q branch F) :=
  (NativeMaskReductionBackend.registration G).certifyWitness (Nat → Nat)
    (fun F code resources cap => resources.1.WithinPeak NativeMaskReductionBackend.runtime measure cap F code)
    F (NativeMaskReductionBackend.adversary G Q branch F)
    (NativeMaskReductionBackend.witness G Q branch observerCap F hEntry hHalt hCap hWidth hObserver)
    (bitCap G Q.code observerCap) (peak G Q branch observerCap F hWidth hObserver)

include hWidth hObserver hEntry hHalt hCap in
theorem witness_code :
    (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).code = Q.code := rfl

include hWidth hObserver hEntry hHalt hCap in
theorem witness_queries :
    (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).resources.1.2 = (fun _ => 1) := rfl

include hWidth hObserver hEntry hHalt hCap in
theorem witness_bitCap :
    (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).resources.2 =
      bitCap G Q.code observerCap := rfl

include hWidth hObserver hEntry hHalt hCap in
theorem witness_peak :
    (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).resources.1.1.WithinPeak
      NativeMaskReductionBackend.runtime measure
      (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).resources.2 F
      (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).code :=
  (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).executes.2

include hWidth hObserver hEntry hHalt hCap in
theorem witness_advantage (n : Nat) :
    (registration G).nativeAdvantage F
      (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).code
      (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).resources n =
    G.prgGoal.advantage n (F n) (G.reduce (F n) branch (fun ciphertext => observer Q ciphertext.toList)) := by
  exact ((registration G).realizes_advantage F (NativeMaskReductionBackend.adversary G Q branch F)
    _ _ (witness G Q branch observerCap F hWidth hObserver hEntry hHalt hCap).realizes n).symm

end Foundation.Symmetric.EncryptThenMAC.NativeMaskReductionSpaceBackend
