import Foundation.Crypto.Semantics.Machine.GeneratedBlockEncryption
import Foundation.Crypto.Semantics.Machine.StructuredCodeEncoding

/-! Computable instruction sequence of the proved fresh-key encryption.
Expose code independently of the noncomputable probability contracts so
resource constants and external execution can evaluate the same program. -/
namespace Machine.GeneratedBlockEncryption

def fixedCode : Program :=
  (((((NativeFlaggedRequest.code.followedBy rewindBitstring).followedBy OneTimePad.keygen).followedBy
    eraseOutputBlock.swapTapes).followedBy rewindBitstring.swapTapes).followedBy
    FlaggedBlockXor.code.swapTapes).followedBy eraseOutputBlock

theorem fixedCode_eq : fixedCode = link.code := rfl

theorem fixedCode_length : fixedCode.length = 94 := by rw [fixedCode_eq]; exact code_length

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fixedCode_encoding_length : (StructuredCodeEncoding.program.encode fixedCode).length = 18331 := by
  decide

end Machine.GeneratedBlockEncryption
