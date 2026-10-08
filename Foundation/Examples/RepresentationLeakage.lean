import Foundation.Crypto.Semantics.Machine.NativeFixedComponent
import Foundation.Crypto.Semantics.Machine.NativeRepresentationObservation

/-! Redundant blank padding can expose a secret to a faithful encoding
observer, despite identical cells and identical actual stopping time.
This is a one-step native counterexample to dropping representation metadata,
not a counterexample to the concrete generated encryption scheme. -/
namespace Foundation.Examples.RepresentationLeakage
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def initial (secret : Bool) : Configuration :=
  {inputTape := {right := if secret then [none] else []}}

def finish (secret : Bool) : Configuration := {initial secret with halted := true}

noncomputable def component : NativeComponent Bool Configuration :=
  NativeComponent.ofFixed [.halt] initial (fun _ state => state)
    (fun secret => PMF.pure (finish secret)) (fun _ => 1)
    (fun secret => by simp [evalConfigWithin, stepPMF, next, initial, finish,
      Instruction.next, PMF.pure_bind, PMF.pure_map])
    (by decide) (fun _ => by change 0 < 1; decide) (fun _ => rfl)
    (by intro secret state h; rw [PMF.mem_support_pure_iff] at h; subst state; rfl)

theorem actual_joint (secret : Bool) :
    component.firstArrival.procedure.execution.costed secret = PMF.pure (finish secret, 1) := by
  rw [component.firstArrival_costed]
  change runToBoundary (stepPMF [.halt]) Configuration.halted 1 (initial secret) = _
  simp [runToBoundary, stepPMF, next, initial, finish, Instruction.next, PMF.pure_bind, PMF.pure_map]

theorem same_cells : (finish false).Equivalent (finish true) := by
  exact ⟨rfl, rfl, (Tape.blank_padding_equivalent [] 1).symm, Tape.Equivalent.refl _⟩

theorem same_bits_and_time (secret : Bool) :
    (component.firstArrival.procedure.execution.costed secret).map
      (fun result => (result.1.inputTape.bits, result.2)) = PMF.pure ([], 1) := by
  rw [actual_joint, PMF.pure_map]
  cases secret <;> simp [finish, initial, Tape.bits]

theorem different_layout : (finish false).layout ≠ (finish true).layout := by decide

def encoded (secret : Bool) : List Bool :=
  NativeEncodedResources.completeEncoding.encode ([.halt], finish secret)

theorem different_encoding : encoded false ≠ encoded true := by
  intro h
  have hState := congrArg Prod.snd (NativeEncodedResources.completeEncoding.encode_injective h)
  exact different_layout (congrArg Configuration.layout hState)

def encodedObserver (state : Configuration) : Bool :=
  decide (NativeEncodedResources.completeEncoding.encode ([.halt], state) = encoded true)

theorem encoded_observation (secret : Bool) :
    (component.firstArrival.procedure.execution.costed secret).map
      (fun result => encodedObserver result.1) = PMF.pure secret := by
  rw [actual_joint, PMF.pure_map]
  change PMF.pure (decide (encoded secret = encoded true)) = PMF.pure secret
  cases secret <;> simp [different_encoding]

end Foundation.Examples.RepresentationLeakage
