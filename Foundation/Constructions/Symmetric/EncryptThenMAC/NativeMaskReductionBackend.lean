import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskChallenge
import Foundation.Crypto.Logic.General.CountedContractObservedBackend
import Foundation.Crypto.Logic.General.Backends
import Foundation.Crypto.Logic.General.ConstrainedObservedExecution

/-! Register both PRG reductions with genuine finite-code execution and one
external-query bounds. The runtime is the explicit challenge/loading/masking
controller around the supplied native code, not an unproved flattening into
a single native program. Public flagged message preparation is an entry layout
precondition inherited from the response-processing runtime. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativeMaskReductionBackend
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC Foundation.Examples
open ReusableBlockPad.NativeObserver (publicCaller observer)
open CryptoLogic.General ContractObservedBackend
universe u
set_option backward.isDefEq.respectTransparency false

structure Context where
  width : Nat
  distribution : PMF (Bits width)
  message : Bits width

noncomputable def runtime : Runtime Backends.system .native where
  Context := Context
  State := NativeMaskChallenge.Control
  step := fun code context => NativeMaskChallenge.step context.distribution context.message code
  initial := fun _ _ => .querying
  terminal := fun _ _ => NativeMaskChallenge.terminal
  absorb := fun code context => NativeMaskChallenge.absorbing context.distribution context.message code
  observe := fun _ _ => NativeMaskChallenge.result

noncomputable def modelGame (G : Generator) (F : InstanceFamily G.prgGoal)
    (A : AdversaryFamily G.prgGoal F) (n : Nat) (world : Bool) : PMF Bool :=
  (if world then G.ideal n else G.real n).bind (A n)

theorem advantage_eq (G : Generator) (F : InstanceFamily G.prgGoal)
    (A : AdversaryFamily G.prgGoal F) (n : Nat) :
    advantageProfile G.prgGoal F A n =
      probabilityGap (eventProb (modelGame G F A n false) (· = true))
        (eventProb (modelGame G F A n true) (· = true)) := rfl

noncomputable def baseRegistration (G : Generator) :=
  Counted.registration runtime (fun _ _ => NativeMaskChallenge.queryEvent) (modelGame G) (advantage_eq G)

/-- Prevent a profile from replacing the PRG oracle by an arbitrary response
law or supplying side-dependent hidden advice through its public context. -/
def FaithfulContext (G : Generator) (F : InstanceFamily G.prgGoal)
    (r : Profile G.prgGoal runtime) : Prop :=
  ∃ branch : Bool, ∀ n world,
    r.context n (F n) world =
      ⟨G.outputLength n, if world then G.ideal n else G.real n, G.message (F n) branch⟩

noncomputable def registration (G : Generator) :=
  (baseRegistration G).restrict (fun F _ resources => FaithfulContext G F resources.1)

variable (G : Generator) {Output : Type u} (Q : Machine.Procedure Machine.Configuration Output)
    (branch : Bool) (observerCap : Nat → Nat)

noncomputable def adversary (F : InstanceFamily G.prgGoal) : AdversaryFamily G.prgGoal F :=
  fun n => G.reduce (F n) branch (fun ciphertext => observer Q ciphertext.toList)

noncomputable def profile : Profile G.prgGoal runtime where
  context := fun n messages world =>
    ⟨G.outputLength n, if world then G.ideal n else G.real n, G.message messages branch⟩
  horizon := fun n => 52 * G.outputLength n + 42 + observerCap n
  logicalGame := fun _ n messages world =>
    (if world then G.ideal n else G.real n).bind
      (G.reduce messages branch (fun ciphertext => observer Q ciphertext.toList))

variable (F : InstanceFamily G.prgGoal)
    (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (hCap : ∀ n ciphertext, ciphertext.length = G.outputLength n →
      Q.execution.budget (publicCaller ciphertext) ≤ observerCap n)
    (hWidth : PolynomiallyBounded G.outputLength) (hObserver : PolynomiallyBounded observerCap)

include hEntry hHalt hCap hWidth hObserver in
theorem executes : (profile G Q branch observerCap).ExecutesWithin runtime F Q.code := by
  refine ⟨NativeMaskChallenge.time_polynomial hWidth hObserver, ?_⟩
  intro n world
  let distribution := if world then G.ideal n else G.real n
  let message := G.message (F n) branch
  let C := NativeMaskChallenge.completion distribution message Q hEntry hHalt (observerCap n) (hCap n)
  refine ⟨C, ?_, ?_⟩
  · change (NativeMaskChallenge.whole distribution message Q hEntry (observerCap n) (hCap n)).budget () ≤ _
    rw [NativeMaskChallenge.budget]
    exact Nat.le_refl _
  · change (C.execution.semantics ()).map NativeMaskChallenge.result = _
    rw [NativeMaskChallenge.completion_game]
    change distribution.bind _ = distribution.bind _
    congr 1
    funext challenge
    unfold Generator.reduce OneTimePad.encrypt
    rw [Bits.xor_comm]

theorem one_query : Counted.WithinEvents runtime (fun _ _ => NativeMaskChallenge.queryEvent)
    (profile G Q branch observerCap) (fun _ => 1) F Q.code := by
  refine ⟨PolynomiallyBounded.const 1, ?_⟩
  intro n world elapsed _ target ht
  exact NativeMaskChallenge.at_most_one_query
    (if world then G.ideal n else G.real n) (G.message (F n) branch) Q.code elapsed target ht

include hEntry hHalt hCap hWidth hObserver in
/-- Nonvacuous class membership for each branch, using the very same fixed
finite observer code and the explicit operational wrapper. -/
noncomputable def witness :
    (registration G).object.Witness F (adversary G Q branch F) :=
  (baseRegistration G).restrictWitness (fun F _ resources => FaithfulContext G F resources.1)
    F (adversary G Q branch F)
    (Counted.witness runtime (fun _ _ => NativeMaskChallenge.queryEvent) (modelGame G) (advantage_eq G)
      F (adversary G Q branch F) Q.code (profile G Q branch observerCap) (fun _ => 1)
      (executes G Q branch observerCap F hEntry hHalt hCap hWidth hObserver)
      (one_query G Q branch observerCap F) (fun _ _ => rfl))
    ⟨branch, fun _ _ => rfl⟩

include hEntry hHalt hCap hWidth hObserver in
theorem witness_code :
    (witness G Q branch observerCap F hEntry hHalt hCap hWidth hObserver).code = Q.code := rfl

include hEntry hHalt hCap hWidth hObserver in
theorem witness_queries :
    (witness G Q branch observerCap F hEntry hHalt hCap hWidth hObserver).resources.2 = (fun _ => 1) := rfl

include hEntry hHalt hCap hWidth hObserver in
/-- Each registered game's advantage is exactly the PRG reduction advantage
used in the encryption theorem, not merely an unrelated executable game. -/
theorem witness_advantage (n : Nat) :
    (registration G).nativeAdvantage F
      (witness G Q branch observerCap F hEntry hHalt hCap hWidth hObserver).code
      (witness G Q branch observerCap F hEntry hHalt hCap hWidth hObserver).resources n =
    G.prgGoal.advantage n (F n) (G.reduce (F n) branch (fun ciphertext => observer Q ciphertext.toList)) := by
  exact ((registration G).realizes_advantage F (adversary G Q branch F)
    _ _ (witness G Q branch observerCap F hEntry hHalt hCap hWidth hObserver).realizes n).symm

end Foundation.Symmetric.EncryptThenMAC.NativeMaskReductionBackend
