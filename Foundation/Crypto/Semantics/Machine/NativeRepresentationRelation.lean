import Foundation.Crypto.Semantics.Machine.NativeEquivalentEntry
import Foundation.Crypto.Semantics.Machine.TapeSwapProcedure

/-! Reusable full-state relations for composing contracts on different
finite representations of the same cells. These are proof operations. -/
namespace Machine.Configuration

theorem Equivalent.trans {first middle last : Configuration}
    (hFirst : first.Equivalent middle) (hLast : middle.Equivalent last) : first.Equivalent last :=
  ⟨hFirst.1.trans hLast.1, hFirst.2.1.trans hLast.2.1,
    hFirst.2.2.1.trans hLast.2.2.1, hFirst.2.2.2.trans hLast.2.2.2⟩

theorem Equivalent.resumeAt {first second : Configuration} (h : first.Equivalent second) (pc : Nat) :
    (first.resumeAt pc).Equivalent (second.resumeAt pc) :=
  ⟨rfl, rfl, h.2.2⟩

theorem Equivalent.swapTapes {first second : Configuration} (h : first.Equivalent second) :
    first.swapTapes.Equivalent second.swapTapes :=
  ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

end Machine.Configuration

namespace Machine.NativeComponent
open Foundation.Probability
universe u v
variable {Input : Type u} {Output : Type v} (P : NativeComponent Input Output)

/-- Every actual exit is related to some supported canonical exit, even
when the original component has a genuinely random result distribution. -/
theorem equivalentEntries_supported_exit (input : EquivalentInput P) (target : Configuration)
    (hTarget : target ∈ (P.equivalentEntries.procedure.execution.semantics input).support) :
    ∃ output, output ∈ (P.procedure.execution.semantics input.logical).support ∧
      target.Equivalent (P.procedure.execution.exit input.logical output) := by
  apply P.equivalentEntries_postcondition input
    (fun state => ∃ output, output ∈ (P.procedure.execution.semantics input.logical).support ∧
      state.Equivalent (P.procedure.execution.exit input.logical output))
    (fun _ _ h => ⟨fun ⟨output, hOutput, hc⟩ => ⟨output, hOutput, h.symm.trans hc⟩,
      fun ⟨output, hOutput, hd⟩ => ⟨output, hOutput, h.trans hd⟩⟩) _ target hTarget
  intro output hOutput
  exact ⟨output, hOutput, Configuration.Equivalent.refl _⟩

/-- A deterministic canonical result gives a full cell-equivalence
postcondition on every actual result, without discarding either tape. -/
theorem equivalentEntries_exit (input : EquivalentInput P) (output : Output)
    (hPure : P.procedure.execution.semantics input.logical = PMF.pure output)
    (target : Configuration)
    (hTarget : target ∈ (P.equivalentEntries.procedure.execution.semantics input).support) :
    target.Equivalent (P.procedure.execution.exit input.logical output) := by
  apply P.equivalentEntries_postcondition input
    (fun state => state.Equivalent (P.procedure.execution.exit input.logical output))
    (fun _ _ h => ⟨fun hc => h.symm.trans hc, fun hd => h.trans hd⟩) _ target hTarget
  intro result hResult
  rw [hPure, PMF.mem_support_pure_iff] at hResult
  subst result
  exact Configuration.Equivalent.refl _

end Machine.NativeComponent
