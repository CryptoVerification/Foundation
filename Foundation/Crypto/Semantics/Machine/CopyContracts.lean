import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.Machine.RetainedCopy
import Foundation.Crypto.Semantics.Machine.SegmentCopy

/-! Existing cell-level copy routines implement reusable execution contracts.
Complete physical prefixes, suffixes, padding and head positions are retained.
Entrances are preconditions on real tapes, never free packet preparation. -/
namespace Machine.CopyContracts
open Foundation.Probability

structure RetainedInput where
  payload : List Bool
  before : List (Option Bool)

noncomputable def retained : Machine.Procedure RetainedInput Unit :=
  Machine.Procedure.ofFixed RetainedCopy.code
    (fun input => RetainedCopy.copying [] input.payload input.before)
    (fun input _ => RetainedCopy.finish input.payload input.before)
    (fun _ => PMF.pure ()) (fun input => 8 * input.payload.length + 5)
    (fun input => by simpa only [PMF.pure_map] using RetainedCopy.run input.payload input.before)

structure SegmentInput where
  beforeInput : List (Option Bool)
  beforeOutput : List (Option Bool)
  afterInput : List (Option Bool)
  payload : List Bool
  blanks : Nat

noncomputable def segment : Machine.Procedure SegmentInput Unit :=
  Machine.Procedure.ofFixed copyBitstring
    (fun input => copySegmentStart input.beforeInput input.beforeOutput input.afterInput input.payload input.blanks)
    (fun input _ => copySegmentFinish input.beforeInput input.beforeOutput input.afterInput input.payload input.blanks)
    (fun _ => PMF.pure ()) (fun input => copyBitstringSteps input.payload)
    (fun input => by
      simpa only [PMF.pure_map] using
        (copySegment_runs input.beforeInput input.beforeOutput input.afterInput input.payload input.blanks).evalConfigWithin_eq_pure_of_no_randomBit
          copyBitstring_no_randomBit)

theorem segment_budget (input : SegmentInput) :
    segment.execution.budget input ≤ 6 * input.payload.length + 2 := copyBitstringSteps_le input.payload

theorem segment_tail (input : SegmentInput) :
    (segment.execution.exit input ()).inputTape.right = input.afterInput := rfl

theorem retained_source (input : RetainedInput) :
    (retained.execution.exit input ()).inputTape.Equivalent (Tape.ofBits input.payload) :=
  RetainedCopy.key_restored input.payload input.before

end Machine.CopyContracts
