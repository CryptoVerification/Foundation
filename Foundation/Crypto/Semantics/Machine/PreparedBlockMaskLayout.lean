import Foundation.Crypto.Semantics.Machine.PreparedBlockMask
import Foundation.Crypto.Semantics.Machine.NativeRepresentationRelation

/-! Full cell-equivalence at the actual compiled masker's exit, including
the retained secret scratch tape. No physical endpoint is replaced. -/
namespace Machine.PreparedBlockMask
open Foundation.Probability

def canonicalExit (input : Input) : Configuration :=
  { (FlaggedBlockXor.final input.key input.message).swapTapes.resumeAt 66 with halted := true }

theorem exit_equivalent (input : Input) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics input).support) :
    target.Equivalent (canonicalExit input) := by
  rw [semantics, PMF.mem_support_map_iff] at hTarget
  obtain ⟨middle, hMiddle, rfl⟩ := hTarget
  have h := FlaggedBlockXor.Component.component.swapTapes.equivalentEntries_exit (maskInput input)
    (FlaggedBlockXor.final input.key input.message) rfl middle hMiddle
  exact (h.resumeAt 66).withHalted true

end Machine.PreparedBlockMask
