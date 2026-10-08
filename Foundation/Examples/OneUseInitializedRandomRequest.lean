import Foundation.Examples.OneUseRandomRequest
import Foundation.Crypto.Semantics.Oracle.OneUseProgramInitialization

/-! Native private-key generation precedes the actual finite caller's local
coin, physical request handling and halt. The key width is arbitrary; requests
whose length differs from that width follow real rejection and recovery. -/
namespace Foundation.OneUseInitializedRandomRequestExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (oracle : BitOracle State) (input : List Bool) (state : State)
    (trace : List (List Bool × List Bool))

def caller : Configuration State :=
  ⟨state, .running (OneUseRandomRequestExamples.initialMachine input), trace⟩

noncomputable def consumer {width : Nat} (key : Bits width) :
    OneUseProgramContract.Consumer Machine.OneTimePad.Prepared.listProcedure.code
      OneUseRandomRequestExamples.code oracle (caller input state trace) (OneUseProgramInitialization.store key) where
  execution := (OneUseRandomRequestExamples.complete oracle false key.toList [] input state trace).physical
  entry := rfl
  exit := fun _ => rfl
  stops := by
    intro physical hs
    change physical ∈ (((OneUseRandomRequestExamples.complete oracle false key.toList [] input state trace).semantics ()).map
      ((OneUseRandomRequestExamples.complete oracle false key.toList [] input state trace).exit ())).support at hs
    rw [OneUseRandomRequestExamples.complete_semantics, PMF.map_comp, PMF.mem_support_map_iff] at hs
    obtain ⟨bit, _, he⟩ := hs
    subst physical
    rfl

noncomputable def complete (width : Nat) :=
  OneUseProgramInitialization.complete Machine.OneTimePad.Prepared.listProcedure.code OneUseRandomRequestExamples.code
    oracle (caller input state trace) width (consumer oracle input state trace)
    (2 + (33 * (width + 1) + 33)) (fun key => by
      change (OneUseRandomRequestExamples.complete oracle false key.toList [] input state trace).budget () ≤ _
      rw [OneUseRandomRequestExamples.complete_budget]
      simp)

theorem budget (width : Nat) : (complete oracle input state trace width).budget () = 39 * width + 73 := by
  rw [complete, OneUseProgramInitialization.budget]
  omega

theorem consumer_semantics {width : Nat} (key : Bits width) :
    (consumer oracle input state trace key).execution.semantics () =
      sampleBit.map (OneUseRandomRequestExamples.halted false key.toList [] input state trace) := by
  change ((OneUseRandomRequestExamples.complete oracle false key.toList [] input state trace).semantics ()).map
    ((OneUseRandomRequestExamples.complete oracle false key.toList [] input state trace).exit ()) = _
  rw [OneUseRandomRequestExamples.complete_semantics, PMF.map_comp]
  rfl

/-- Final distribution after the entire physically initialized caller. -/
theorem run (width horizon : Nat) (hBudget : 39 * width + 73 ≤ horizon) :
    TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen
      Machine.OneTimePad.Prepared.listProcedure.code OneUseRandomRequestExamples.code oracle (caller input state trace))
      horizon (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      (uniform (Bits width)).bind (fun key =>
        sampleBit.map (OneUseInitialization.Control.active ∘
          OneUseRandomRequestExamples.halted false key.toList [] input state trace)) := by
  have h := OneUseProgramInitialization.run Machine.OneTimePad.Prepared.listProcedure.code OneUseRandomRequestExamples.code
    oracle (caller input state trace) width (consumer oracle input state trace)
    (2 + (33 * (width + 1) + 33)) (fun key => by
      change (OneUseRandomRequestExamples.complete oracle false key.toList [] input state trace).budget () ≤ _
      rw [OneUseRandomRequestExamples.complete_budget]
      simp) horizon (by omega)
  simp_rw [consumer_semantics] at h
  simpa only [PMF.map_comp] using h

end Foundation.OneUseInitializedRandomRequestExamples
