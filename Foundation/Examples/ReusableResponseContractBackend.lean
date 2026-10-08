import Foundation.Examples.ReusableResponseTwoQueriesPotential
import Foundation.Crypto.Logic.General.ContractObservedBackend
import Foundation.Crypto.Logic.General.Backends

/-! An inhabited operational registration of the actual two-query runtime.
The full finite-code/state peak bound and genuine final stopping contract use
the same code, context and horizon. Logical-goal realization is still an
explicit obligation; the acknowledgement example is not a cipher proof. -/
namespace Foundation.Examples.ReusableResponseContractBackend
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
open CryptoLogic.General ContractObservedBackend
universe u v
set_option backward.isDefEq.respectTransparency false

structure Context (State : Type v) where
  oracle : BitOracle State
  key : List Bool
  state : State
  trace : List (List Bool × List Bool)
  request : List Bool

def terminal {State : Type v} : ReusableResponse.Control State → Prop
  | .source _ frame => Reification.terminal frame.control = true
  | _ => False

def observe {State : Type v} : ReusableResponse.Control State → Bool
  | .source _ ⟨_, .running machine, _⟩ => machine.outputTape.current.getD false
  | .source _ ⟨_, .finished bit, _⟩ => bit
  | _ => false

noncomputable def runtime (State : Type v) : Runtime Backends.system .interactive where
  Context := Context State
  State := ReusableResponse.Control State
  step := fun code context => ReusableResponse.step ReusableResponseTwoQueries.native code context.oracle
  initial := fun _ context => .source (retainedKey context.key)
    ⟨context.state, .running (ReusableResponseTwoQueries.caller context.request), context.trace⟩
  terminal := fun _ _ => terminal
  absorb := by
    intro code context target h
    cases target with
    | source key frame =>
        cases hc : frame.control <;>
          simp_all [terminal, ReusableResponse.step, ReusableResponseSource.step,
            Reification.timedStep, Reification.terminal, PMF.pure_map]
    | processing => contradiction
    | calling => contradiction
  observe := fun _ _ => observe

variable {State : Type v} (context : Context State)

noncomputable def completion : Completion
    ((runtime State).step ReusableResponseTwoQueries.code context)
    ((runtime State).initial ReusableResponseTwoQueries.code context)
    ((runtime State).terminal ReusableResponseTwoQueries.code context) :=
  Completion.ofProcedure
    ((ReusableResponseTwoQueries.Potential.whole context.oracle context.key context.state context.trace context.request).reindex
      (fun _ : Unit => .first)) rfl
    (by
      intro output h
      change output ∈ ((ReusableResponseTwoQueries.Potential.whole context.oracle context.key context.state context.trace context.request).semantics .first).support at h
      rw [ReusableResponseTwoQueries.Potential.whole_semantics, PMF.mem_support_pure_iff] at h
      subst output
      change Reification.terminal (.running (ReusableResponseTwoQueries.finalCaller context.request)) = true
      rfl)

noncomputable def profile (P : CryptoGoal.{u}) : Profile P (runtime State) where
  context := fun _ _ _ => context
  horizon := fun _ => 18 * context.key.length + 5 * context.request.length + 66
  logicalGame := fun _ _ _ _ => PMF.pure false

variable {P : CryptoGoal.{u}} (F : InstanceFamily P)

theorem executes : (profile context P).ExecutesWithin (runtime State) F ReusableResponseTwoQueries.code := by
  refine ⟨PolynomiallyBounded.const _, ?_⟩
  intro n side
  refine ⟨completion context, ?_, ?_⟩
  · change (ReusableResponseTwoQueries.Potential.whole context.oracle context.key context.state context.trace context.request).budget .first ≤ _
    rw [ReusableResponseTwoQueries.Potential.budget]
    exact Nat.le_refl _
  · rw [completion, Completion.ofProcedure_semantics]
    change (((ReusableResponseTwoQueries.Potential.whole context.oracle context.key context.state context.trace context.request).semantics .first).map _).map _ = PMF.pure false
    rw [ReusableResponseTwoQueries.Potential.whole_semantics, PMF.pure_map, PMF.pure_map]
    rfl

variable (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (context.oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

def measure (code : CryptoOracle.Interactive.Code) (_ : Context State) (target : ReusableResponse.Control State) :=
  ((ReusableResponse.Encoded.completeEncoding E).encode
    (PrivateKeyCopy.code, ReusableResponseTwoQueries.native, code, target)).length

def bitCap : Nat → Nat := fun _ =>
  ReusableResponseTwoQueries.bitBound stateSize context.key context.state context.trace context.request stateIncrement responseCap

include hState hOracle in
theorem peak : (profile context P).WithinPeak (runtime State) (measure E)
    (bitCap context stateSize stateIncrement responseCap) F ReusableResponseTwoQueries.code := by
  refine ⟨?_, ?_⟩
  · exact PolynomiallyBounded.const
      (ReusableResponseTwoQueries.bitBound stateSize context.key context.state context.trace context.request stateIncrement responseCap)
  intro n side elapsed hElapsed target hTarget
  exact ReusableResponseTwoQueries.encoded_prefix E stateSize hState context.oracle context.key context.state
    context.trace context.request stateIncrement responseCap hOracle elapsed hElapsed target hTarget

variable (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))

include hState hOracle in
noncomputable def witness (A : AdversaryFamily P F)
    (hModel : ∀ n side, PMF.pure false = modelGame F A n side) :
    (peakRegistration (runtime State) modelGame hAdvantage (measure E)).object.Witness F A :=
  peakWitness (runtime State) modelGame hAdvantage (measure E) F A ReusableResponseTwoQueries.code
    (profile context P) (bitCap context stateSize stateIncrement responseCap)
    (executes context F) (peak context F E stateSize hState stateIncrement responseCap hOracle) hModel

end Foundation.Examples.ReusableResponseContractBackend
