import Foundation.Crypto.Semantics.Machine.NativeContinuationResources
import Foundation.Crypto.Semantics.Machine.ControllerExtent

/-! Local resource measures across a producer/native handoff. These measures
retain the producer even while native code is running, and can be composed
with preceding query or loading controllers without assuming termination. -/
namespace Machine.NativeContinuation.Growth
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def extent (sourceExtent : State → Nat) : Control State → Nat
  | .producing state => sourceExtent state
  | .observing saved machine => max (sourceExtent saved) (ControllerExtent.machine machine)

def pc (sourcePc : State → Nat) : Control State → Nat
  | .producing state => sourcePc state
  | .observing saved machine => max (sourcePc saved) machine.pc

variable (sourceStep : State → PMF State) (boundary : State → Bool)
    (publicMachine : State → Configuration) (code : Program)

theorem extent_step (sourceExtent : State → Nat) (increment publicExtra : Nat)
    (hSource : ∀ start next, next ∈ (sourceStep start).support →
      sourceExtent next ≤ sourceExtent start + increment)
    (hPublic : ∀ state, boundary state = true →
      ControllerExtent.machine (publicMachine state) ≤ sourceExtent state + publicExtra)
    (start next : Control State)
    (h : next ∈ (step sourceStep boundary publicMachine code start).support) :
    extent sourceExtent next ≤ extent sourceExtent start + (increment + publicExtra + 1) := by
  cases start with
  | producing state =>
      cases hb : boundary state with
      | true =>
          simp only [step, hb, ↓reduceIte, PMF.mem_support_pure_iff] at h
          subst next
          have hp := hPublic state hb
          simp only [extent, Configuration.resumeAt, ControllerExtent.machine] at *
          omega
      | false =>
          simp only [step, hb, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hs := hSource state next hn
          simp only [extent]
          omega
  | observing saved machine =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, rfl⟩ := h
      have hn := ControllerExtent.native_bound code machine next hn
      simp only [extent]
      omega

theorem pc_step (sourcePc : State → Nat) (increment : Nat)
    (hSource : ∀ start next, next ∈ (sourceStep start).support →
      sourcePc next ≤ sourcePc start + increment)
    (start next : Control State)
    (h : next ∈ (step sourceStep boundary publicMachine code start).support) :
    pc sourcePc next ≤ pc sourcePc start + (increment + code.addressCap + 1) := by
  cases start with
  | producing state =>
      cases hb : boundary state with
      | true =>
          simp only [step, hb, ↓reduceIte, PMF.mem_support_pure_iff] at h
          subst next
          simp [pc, Configuration.resumeAt]
      | false =>
          simp only [step, hb, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hs := hSource state next hn
          simp only [pc]
          omega
  | observing saved machine =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, rfl⟩ := h
      have hn := pc_le_of_support code machine next hn
      simp only [pc]
      omega

end Machine.NativeContinuation.Growth
