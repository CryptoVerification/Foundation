import Foundation.Examples.ReusableBlockPadResources
import Foundation.Crypto.Logic.General.ContractObservedBackend
import Foundation.Crypto.Logic.General.Backends

/-! An inhabited general-logic registration of the actual arbitrary-width
pad experiment. The observation is a mathematical predicate of ciphertext
bytes; no running-time claim is made for computing that predicate. -/
namespace Foundation.Examples.ReusableBlockPadBackend
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
open CryptoLogic.General ContractObservedBackend
open scoped ENNReal
universe v
set_option backward.isDefEq.respectTransparency false

structure Context (State : Type v) where
  oracle : BitOracle State
  state : State
  trace : List (List Bool × List Bool)
  width : Nat
  message : Bits width
  observer : List Bool → Bool

def terminal {State : Type v} : ReusableResponseInitialization.Control ResponseHandoff.Control State → Prop
  | .active (.source _ frame) => Reification.terminal frame.control = true
  | _ => False

noncomputable def runtime (State : Type v) : Runtime Backends.system .interactive where
  Context := Context State
  State := ReusableResponseInitialization.Control ResponseHandoff.Control State
  step := fun code c => ReusableResponseInitialization.step ReusableBlockPad.componentStep
    ReusableResponse.begin ReusableBlockPad.ready Machine.OneTimePad.keygen FlaggedBlockXor.code code c.oracle
    (ReusableBlockPad.callerFrame c.state c.trace c.message)
  initial := fun _ c => .initializing (.generating (Machine.Configuration.initial (List.replicate c.width true)))
  terminal := fun _ _ => terminal
  absorb := by
    intro code c target h
    cases target with
    | initializing => contradiction
    | aligning => contradiction
    | active source =>
        cases source with
        | processing => contradiction
        | calling => contradiction
        | source key frame =>
            cases hc : frame.control <;>
              simp_all [terminal, ReusableResponseInitialization.step, ReusableResponseSource.step,
                Reification.timedStep, Reification.terminal, PMF.pure_map]
  observe := fun _ c target => c.observer (ReusableBlockPad.observe target)

variable {State : Type v} (c : Context State)

noncomputable def completion : Completion
    ((runtime State).step ReusableBlockPad.code c)
    ((runtime State).initial ReusableBlockPad.code c)
    ((runtime State).terminal ReusableBlockPad.code c) :=
  Completion.ofProcedure (ReusableBlockPad.initialized c.oracle c.state c.trace c.message) rfl
    (by
      intro result hr
      rw [ReusableBlockPad.initialized_semantics, PMF.mem_support_map_iff] at hr
      obtain ⟨key, _, rfl⟩ := hr
      change Reification.terminal (.running (ReusableBlockPad.finalCaller key c.message)) = true
      rfl)

theorem completion_budget : (completion c).execution.budget () = 55 * c.width + 41 :=
  ReusableBlockPad.initialized_budget c.oracle c.state c.trace c.message

theorem completion_game :
    ((completion c).execution.semantics ()).map ((runtime State).observe ReusableBlockPad.code c) =
      (uniform (Bits c.width)).map (fun key => c.observer (OneTimePad.encrypt key c.message).toList) := by
  have ht : (completion c).execution.budget () ≤ 55 * c.width + 41 := by rw [completion_budget]
  rw [← (completion c).final_run ((runtime State).absorb ReusableBlockPad.code c) _ ht]
  change (TimedExecution.eval (ReusableBlockPad.step c.oracle c.state c.trace c.message) (55 * c.width + 41)
    (.initializing (.generating (Machine.Configuration.initial (List.replicate c.width true))))).map
      (fun target => c.observer (ReusableBlockPad.observe target)) = _
  have h := congrArg (fun p : PMF (List Bool) => p.map c.observer)
    (ReusableBlockPad.ciphertext_eq c.oracle c.state c.trace c.message (55 * c.width + 41) (Nat.le_refl _))
  simpa only [ReusableBlockPad.ciphertext, PMF.map_comp, Function.comp_def] using h

noncomputable def goal (width : Nat → Nat) : CryptoGoal where
  Instance := fun n => Bits (width n) × Bits (width n)
  Adversary := fun _ _ => List Bool → Bool
  advantage := fun n messages observer => probabilityGap
    (eventProb ((uniform (Bits (width n))).map (fun key => observer (OneTimePad.encrypt key messages.1).toList)) (· = true))
    (eventProb ((uniform (Bits (width n))).map (fun key => observer (OneTimePad.encrypt key messages.2).toList)) (· = true))

variable (width : Nat → Nat)

noncomputable def modelGame (F : InstanceFamily (goal width)) (A : AdversaryFamily (goal width) F)
    (n : Nat) (side : Bool) : PMF Bool :=
  (uniform (Bits (width n))).map (fun key =>
    A n (OneTimePad.encrypt key (if side then (F n).2 else (F n).1)).toList)

theorem advantage_eq (F A n) : advantageProfile (goal width) F A n =
    probabilityGap (eventProb (modelGame width F A n false) (· = true))
      (eventProb (modelGame width F A n true) (· = true)) := rfl

private theorem observer_uniform {W : Nat} (message : Bits W) (observer : List Bool → Bool) :
    (uniform (Bits W)).map (fun key => observer (OneTimePad.encrypt key message).toList) =
      (uniform (Bits W)).map (fun bits => observer bits.toList) := by
  have h := congrArg (fun p : PMF (Bits W) => p.map (fun bits => observer bits.toList))
    (OneTimePad.ciphertext_uniform message)
  simpa only [OneTimePad.ciphertext, PMF.map_comp, Function.comp_def] using h

theorem advantage_zero (n : Nat) (messages : (goal width).Instance n)
    (observer : (goal width).Adversary n messages) : (goal width).advantage n messages observer = 0 := by
  change probabilityGap _ _ = 0
  rw [observer_uniform messages.1 observer, observer_uniform messages.2 observer]
  simp [probabilityGap]

theorem negligible_advantage (F : InstanceFamily (goal width)) (A : AdversaryFamily (goal width) F) :
    Negligible (advantageProfile (goal width) F A) := by
  have h : advantageProfile (goal width) F A = fun _ => 0 := by
    funext n
    exact advantage_zero width n (F n) (A n)
  rw [h]
  exact Negligible.zero

variable (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (F : InstanceFamily (goal width)) (A : AdversaryFamily (goal width) F)

def context (n : Nat) (side : Bool) : Context State :=
  ⟨oracle, state, trace, width n, if side then (F n).2 else (F n).1, A n⟩

noncomputable def profile : Profile (goal width) (runtime State) where
  context := fun n _ side => context width oracle state trace F A n side
  horizon := fun n => 55 * width n + 41
  logicalGame := fun _ n _ side => modelGame width F A n side

theorem executes (hWidth : PolynomiallyBounded width) :
    (profile width oracle state trace F A).ExecutesWithin (runtime State) F ReusableBlockPad.code := by
  refine ⟨ReusableBlockPad.time_polynomial hWidth, ?_⟩
  intro n side
  refine ⟨completion (context width oracle state trace F A n side), ?_, ?_⟩
  · rw [completion_budget]
    exact Nat.le_refl _
  · exact completion_game (context width oracle state trace F A n side)

noncomputable def registration := ContractObservedBackend.registration (runtime State)
  (modelGame width) (advantage_eq width)

/-- A concrete finite-code witness exists for every ciphertext predicate,
so the registered class is not empty by construction. -/
noncomputable def witness (hWidth : PolynomiallyBounded width) :
    (registration (State := State) width).object.Witness F A :=
  ContractObservedBackend.witness (runtime State) (modelGame width) (advantage_eq width) F A
    ReusableBlockPad.code (profile width oracle state trace F A)
    (executes width oracle state trace F A hWidth) (fun _ _ => rfl)

theorem witness_code (hWidth : PolynomiallyBounded width) :
    (witness width oracle state trace F A hWidth).code = ReusableBlockPad.code := rfl

/-- The logical perfect-secrecy theorem also applies to the represented
class; existence of actual witnesses is proved separately above. -/
theorem secure : (registration (State := State) width).object.Secure F := by
  intro adversary _
  exact negligible_advantage width F adversary

end Foundation.Examples.ReusableBlockPadBackend
