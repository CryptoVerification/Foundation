import Foundation.Examples.ReusableResponseInitializedTwoQueries
import Foundation.Examples.ReusableResponseContractBackend

/-! Register actual private key generation and both adaptive calls through
the common completed-contract backend. This registers the true operational
clock, including the two charged store-alignment moves. Peak encoding bounds
for the extra initialization phases are a separate obligation. -/
namespace Foundation.Examples.ReusableResponseInitializedBackend
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
open CryptoLogic.General ContractObservedBackend
universe u v
set_option backward.isDefEq.respectTransparency false

structure Context (State : Type v) where
  oracle : BitOracle State
  state : State
  trace : List (List Bool × List Bool)
  request : List Bool
  width : Nat

noncomputable def runtime (State : Type v) : Runtime Backends.system .interactive where
  Context := Context State
  State := ReusableResponseInitialization.Control ResponseHandoff.Control State
  step := fun code c => ReusableResponseInitialization.step
    ReusableResponseInitializedTwoQueries.componentStep ReusableResponse.begin ReusableResponseInitializedTwoQueries.ready
    OneTimePad.keygen ReusableResponseTwoQueries.native code c.oracle
    (ReusableResponseInitializedTwoQueries.callerFrame c.state c.trace c.request)
  initial := fun _ c => .initializing (.generating (Machine.Configuration.initial (List.replicate c.width true)))
  terminal := fun _ _ target => match target with
    | .active source => ReusableResponseContractBackend.terminal source
    | _ => False
  absorb := by
    intro code c target h
    cases target with
    | initializing => contradiction
    | aligning => contradiction
    | active source =>
        change (ReusableResponse.step ReusableResponseTwoQueries.native code c.oracle source).map
          ReusableResponseInitialization.Control.active = _
        have ha := (ReusableResponseContractBackend.runtime State).absorb code
          (⟨c.oracle, [], c.state, c.trace, c.request⟩ : ReusableResponseContractBackend.Context State) source h
        change ReusableResponse.step ReusableResponseTwoQueries.native code c.oracle source = PMF.pure source at ha
        rw [ha, PMF.pure_map]
  observe := fun _ _ target => match target with
    | .active source => ReusableResponseContractBackend.observe source
    | _ => false

variable {State : Type v} (c : Context State)

noncomputable def completion : Completion
    ((runtime State).step ReusableResponseTwoQueries.code c)
    ((runtime State).initial ReusableResponseTwoQueries.code c)
    ((runtime State).terminal ReusableResponseTwoQueries.code c) :=
  Completion.ofProcedure
    (ReusableResponseInitializedTwoQueries.whole c.oracle c.state c.trace c.request c.width) rfl
    (by
      intro result h
      rw [ReusableResponseInitializedTwoQueries.semantics, PMF.mem_support_map_iff] at h
      obtain ⟨key, _, rfl⟩ := h
      rw [ReusableResponseInitializedTwoQueries.exit]
      change Reification.terminal (.running (ReusableResponseTwoQueries.finalCaller c.request)) = true
      rfl)

noncomputable def profile (P : CryptoGoal.{u}) : Profile P (runtime State) where
  context := fun _ _ _ => c
  horizon := fun _ => 24 * c.width + 5 * c.request.length + 72
  logicalGame := fun _ _ _ _ => PMF.pure false

variable {P : CryptoGoal.{u}} (F : InstanceFamily P)

theorem executes : (profile c P).ExecutesWithin (runtime State) F ReusableResponseTwoQueries.code := by
  refine ⟨PolynomiallyBounded.const _, ?_⟩
  intro n side
  refine ⟨completion c, ?_, ?_⟩
  · change (ReusableResponseInitializedTwoQueries.whole c.oracle c.state c.trace c.request c.width).budget () ≤ _
    rw [ReusableResponseInitializedTwoQueries.budget]
    exact Nat.le_refl _
  · rw [completion, Completion.ofProcedure_semantics, ReusableResponseInitializedTwoQueries.semantics,
      PMF.map_comp, PMF.map_comp]
    change (Foundation.Probability.uniform (Foundation.Symmetric.Bits c.width)).map (fun _ => false) = PMF.pure false
    exact PMF.map_const _ _

/-- Contexts may vary with the security parameter, public instance and
experiment side. The sampler and both caller codes remain fixed. -/
noncomputable def familyProfile (contexts : ∀ n, P.Instance n → Bool → Context State)
    (horizon : Nat → Nat) : Profile P (runtime State) where
  context := contexts
  horizon := horizon
  logicalGame := fun _ _ _ _ => PMF.pure false

theorem family_executes (contexts : ∀ n, P.Instance n → Bool → Context State)
    (horizon : Nat → Nat) (hTime : PolynomiallyBounded horizon)
    (hClock : ∀ n side, 24 * (contexts n (F n) side).width +
      5 * (contexts n (F n) side).request.length + 72 ≤ horizon n) :
    (familyProfile contexts horizon).ExecutesWithin (runtime State) F ReusableResponseTwoQueries.code := by
  refine ⟨hTime, ?_⟩
  intro n side
  obtain ⟨C, hb, hg⟩ := (executes (contexts n (F n) side) F).2 n side
  exact ⟨C, hb.trans (hClock n side), hg⟩

theorem time_profile_polynomial {width requestLength : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hRequest : PolynomiallyBounded requestLength) :
    PolynomiallyBounded (fun n => 24 * width n + 5 * requestLength n + 72) :=
  (((PolynomiallyBounded.const 24).mul hWidth).add
    ((PolynomiallyBounded.const 5).mul hRequest)).add (PolynomiallyBounded.const 72)

end Foundation.Examples.ReusableResponseInitializedBackend
