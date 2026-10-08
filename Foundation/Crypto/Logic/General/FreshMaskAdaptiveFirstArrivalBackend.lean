import Foundation.Crypto.Logic.General.FirstArrivalObservedBackend
import Foundation.Crypto.Logic.General.Backends
import Foundation.Crypto.Semantics.Oracle.FreshMaskAdaptivePublicSecurity
import Foundation.Crypto.Semantics.Oracle.FreshMaskAdaptiveResources

/-! Inhabited first-arrival registration of actual repeated native masking.
The fixed native component and the finite caller code are both counted.
Observation is a semantic public event; no implementation or running-time
bound for an arbitrary observer program is asserted. -/
namespace CryptoLogic.General.FreshMaskAdaptiveFirstArrivalBackend
open Foundation.Probability TimedExecution Foundation.Symmetric
open CryptoOracle.Interactive
open FirstArrivalObservedBackend
universe u v
set_option backward.isDefEq.respectTransparency false

structure Context (State : Type v) where
  state : State
  rounds : Nat
  request : List Bool

noncomputable def runtime (State : Type v) (observer : CryptoOracle.Interactive.Control × Nat → Bool) :
    Runtime Backends.system .interactive where
  Context := Context State
  State := PacketResponseSource.Control Machine.NativePacketService.Control State Unit
  step := fun code _ => PacketResponseSource.step FreshMaskCallerService.componentStep
    FreshMaskCallerService.begin FreshMaskCallerService.ready code FreshMaskAdaptiveResources.idleOracle
  initial := fun _ context => .source ()
    (AdaptiveBitstringLoop.frame context.state context.rounds [] context.request [])
  terminal := fun _ _ => PacketResponseSource.terminal
  absorb := fun code _ target ht => PacketResponseSource.terminal_absorbing
    FreshMaskCallerService.componentStep FreshMaskCallerService.begin FreshMaskCallerService.ready
    code FreshMaskAdaptiveResources.idleOracle target ht
  observe := fun _ _ result => observer (FreshMaskAdaptiveExecution.publicControl result.1, result.2)

variable {State : Type v} (observer : CryptoOracle.Interactive.Control × Nat → Bool)
    (P : CryptoGoal.{u}) (rounds width : Nat → Nat) (state : Nat → State)
    (messages : ∀ n, P.Instance n → Bool → Bits (width n))

noncomputable def profile : Profile P (runtime State observer) where
  context := fun n instanceValue side => ⟨state n, rounds n, (messages n instanceValue side).toList⟩
  horizon := fun n => FreshMaskAdaptiveExecution.timeBound (rounds n) (width n)
  jointLaw := fun _ n instanceValue side =>
    (FreshMaskAdaptiveExecution.law (rounds n) (state n) [] (messages n instanceValue side).toList []).map
      (fun frame => (PacketResponseSource.Control.source () frame,
        FreshMaskAdaptiveExecution.timeBound (rounds n) (width n)))

variable {P} (F : InstanceFamily P)

theorem executes (hRounds : PolynomiallyBounded rounds) (hWidth : PolynomiallyBounded width) :
    (profile observer P rounds width state messages).ExecutesWithin (runtime State observer) F
      AdaptiveBitstringLoop.code := by
  refine ⟨FreshMaskAdaptiveExecution.time_polynomial hRounds hWidth, ?_⟩
  intro n side
  constructor
  · have h := FreshMaskAdaptiveExecution.first_halt_joint
      (FreshMaskAdaptiveResources.idleOracle : BitOracle State) (rounds n) (state n) []
      (messages n (F n) side).toList []
    rw [Bits.length_toList] at h
    exact h
  · intro result hr
    change result ∈ ((FreshMaskAdaptiveExecution.law (rounds n) (state n) []
      (messages n (F n) side).toList []).map _).support at hr
    rw [PMF.mem_support_map_iff] at hr
    obtain ⟨frame, hf, rfl⟩ := hr
    exact (FreshMaskAdaptiveExecution.law_support (rounds n) (state n) []
      (messages n (F n) side).toList [] frame hf).1

noncomputable def measure (E : Machine.FiniteBitEncoding State) (code : CryptoOracle.Interactive.Code)
    (_ : Context State) (target : PacketResponseSource.Control Machine.NativePacketService.Control State Unit) : Nat :=
  ((PacketResponseEncoding.completeEncoding Machine.NativePacketService.Resources.encoding E
    FreshMaskAdaptiveResources.unitEncoding).encode
      (code, FreshMaskAdaptiveResources.native, target)).length

noncomputable def bitCap (stateSize : State → Nat) : Nat → Nat := fun n =>
  FreshMaskAdaptiveResources.bitBound (stateSize (state n)) 0 0 (rounds n) (width n)

theorem peak (E : Machine.FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ s, (E.encode s).length ≤ stateSize s)
    (hSize : PolynomiallyBounded (fun n => stateSize (state n)))
    (hRounds : PolynomiallyBounded rounds) (hWidth : PolynomiallyBounded width) :
    (profile observer P rounds width state messages).WithinPeak (runtime State observer) (measure E)
      (bitCap rounds width state stateSize) F AdaptiveBitstringLoop.code := by
  refine ⟨FreshMaskAdaptiveResources.space_polynomial hSize (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.const 0) hRounds hWidth, ?_⟩
  intro n side elapsed he target ht
  have h := FreshMaskAdaptiveResources.peak_closed E stateSize hState (state n) (rounds n)
    (messages n (F n) side).toList elapsed (by simpa only [profile, Bits.length_toList] using he) target ht
  simpa only [measure, bitCap, Bits.length_toList] using h

theorem logicalGame_equal (hPositive : ∀ n, 0 < rounds n) (n : Nat) (instanceValue : P.Instance n) :
    (profile observer P rounds width state messages).logicalGame (runtime State observer)
      AdaptiveBitstringLoop.code n instanceValue false =
    (profile observer P rounds width state messages).logicalGame (runtime State observer)
      AdaptiveBitstringLoop.code n instanceValue true := by
  cases hq : rounds n with
  | zero => have := hPositive n; omega
  | succ q =>
      have h := congrArg (fun distribution => distribution.map
        (fun control => observer (control, FreshMaskAdaptiveExecution.timeBound (q + 1) (width n))))
        (FreshMaskAdaptiveExecution.law_control_plaintext_independence q (state n) []
          (messages n instanceValue false) (messages n instanceValue true) [] [])
      simpa only [Profile.logicalGame, profile, runtime, PMF.map_comp, Function.comp_def,
        FreshMaskAdaptiveExecution.publicControl, hq] using h

variable (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))
    (A : AdversaryFamily P F)

/-- Construct the logic's execution witness from the proved physical runtime. -/
noncomputable def witness (hRounds : PolynomiallyBounded rounds) (hWidth : PolynomiallyBounded width)
    (hLogical : ∀ n side,
      (profile observer P rounds width state messages).logicalGame (runtime State observer)
        AdaptiveBitstringLoop.code n (F n) side = modelGame F A n side) :
    (FirstArrivalObservedBackend.registration (runtime State observer) modelGame hAdvantage).object.Witness F A :=
  FirstArrivalObservedBackend.witness (runtime State observer) modelGame hAdvantage F A
    AdaptiveBitstringLoop.code (profile observer P rounds width state messages)
    (executes observer rounds width state messages F hRounds hWidth) hLogical

/-- Register the same code and game with all-prefix physical storage evidence. -/
noncomputable def peakWitness (E : Machine.FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ s, (E.encode s).length ≤ stateSize s)
    (hSize : PolynomiallyBounded (fun n => stateSize (state n)))
    (hRounds : PolynomiallyBounded rounds) (hWidth : PolynomiallyBounded width)
    (hLogical : ∀ n side,
      (profile observer P rounds width state messages).logicalGame (runtime State observer)
        AdaptiveBitstringLoop.code n (F n) side = modelGame F A n side) :
    (FirstArrivalObservedBackend.peakRegistration (runtime State observer) modelGame hAdvantage
      (measure E)).object.Witness F A :=
  FirstArrivalObservedBackend.peakWitness (runtime State observer) modelGame hAdvantage (measure E)
    F A AdaptiveBitstringLoop.code (profile observer P rounds width state messages)
    (bitCap rounds width state stateSize)
    (executes observer rounds width state messages F hRounds hWidth)
    (peak observer rounds width state messages F E stateSize hState hSize hRounds hWidth) hLogical

include hAdvantage in
/-- Realization is explicit: a goal's advantage is not defined by fiat. -/
theorem advantage_zero (hPositive : ∀ n, 0 < rounds n)
    (hLogical : ∀ n side,
      (profile observer P rounds width state messages).logicalGame (runtime State observer)
        AdaptiveBitstringLoop.code n (F n) side = modelGame F A n side) (n : Nat) :
    advantageProfile P F A n = 0 := by
  rw [hAdvantage, ← hLogical n false, ← hLogical n true,
    logicalGame_equal observer rounds width state messages hPositive n (F n)]
  simp [probabilityGap]

end CryptoLogic.General.FreshMaskAdaptiveFirstArrivalBackend
