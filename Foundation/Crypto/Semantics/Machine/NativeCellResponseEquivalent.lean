import Foundation.Crypto.Semantics.Machine.NativeCellResponse
import Foundation.Crypto.Semantics.Machine.NativeRepresentationRelation

/-! Transport physical packet delivery to an actual cell-equivalent entry.
Both tapes and their represented padding remain untouched. Equivalence
preserves delivered bits and real elapsed time, not represented storage. -/
namespace Machine.NativeCellResponse
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

theorem valid_equivalent (cap : Nat) (first second : Configuration)
    (h : first.Equivalent second) : Valid cap first ↔ Valid cap second := by
  have hb : first.outputBits = second.outputBits := h.2.2.2.bits
  constructor
  · intro hv
    refine ⟨h.2.1.symm.trans hv.1, ?_, ?_⟩
    · rw [← hb]
      exact h.2.2.2.symm.trans hv.2.1
    · rw [← hb]
      exact hv.2.2
  · intro hv
    refine ⟨h.2.1.trans hv.1, ?_, ?_⟩
    · rw [hb]
      exact h.2.2.2.trans hv.2.1
    · rw [hb]
      exact hv.2.2

variable {Argument : Type u} {Result : Type v} (P : NativeComponent Argument Result)
    (input : NativeComponent.EquivalentInput P) (cap : Nat)
    (hValid : ∀ result ∈ (P.procedure.execution.semantics input.logical).support,
      Valid cap (P.procedure.execution.exit input.logical result))

include hValid in
theorem equivalent_supported (state : Configuration)
    (hState : state ∈ (P.equivalentEntries.procedure.execution.semantics input).support) :
    Valid cap (P.equivalentEntries.procedure.execution.exit input state) :=
  P.equivalentEntries_postcondition input (Valid cap) (valid_equivalent cap) hValid state hState

noncomputable def fromEquivalent :=
  whole P.equivalentEntries input cap (equivalent_supported P input cap hValid)

theorem fromEquivalent_entry : (fromEquivalent P input cap hValid).entry () = .running input.actual := rfl

/-- Initial finite padding can change storage but cannot change the joint
law of the exported packet and its actual delivery time. -/
theorem fromEquivalent_costed :
    ((fromEquivalent P input cap hValid).costed ()).map (fun result => (result.1.2, result.2)) =
      (P.firstArrival.procedure.execution.costed input.logical).map
        (fun result => (result.1.outputBits, result.2 + (3 * result.1.outputBits.length + 4))) := by
  rw [fromEquivalent, costed]
  have h := congrArg (fun distribution => distribution.map
    (fun result : List Bool × Nat => (result.1, result.2 + (3 * result.1.length + 4))))
    (P.equivalentEntries_firstArrival_observe input Configuration.outputBits
      (fun _ _ h => h.2.2.2.bits))
  simpa only [PMF.map_comp, Function.comp_def] using h

end Machine.NativeCellResponse
