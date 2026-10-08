import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionRepresentation

/-! Bounded exhaustive exploration of the actual encryption representation.
This checks all messages and all random branches through width four. It is
an executable regression check, not an arbitrary-width layout theorem. -/
namespace Foundation.Examples.GeneratedEncryptionLayoutCheck
open Machine
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def compiledCode : Program :=
  (((((NativeFlaggedRequest.code.followedBy rewindBitstring).followedBy OneTimePad.keygen).followedBy
    eraseOutputBlock.swapTapes).followedBy rewindBitstring.swapTapes).followedBy
    FlaggedBlockXor.code.swapTapes).followedBy eraseOutputBlock

theorem compiledCode_eq : compiledCode = GeneratedBlockEncryption.link.code := rfl

private def allBits : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBits n).flatMap (fun rest => [false :: rest, true :: rest])

private def paths : Nat → Configuration → List (Configuration × Nat)
  | 0, state => [(state, 0)]
  | fuel + 1, state =>
      if state.halted then [(state, 0)] else
        (successors compiledCode state).flatMap (fun next =>
          (paths fuel next).map (fun result => (result.1, result.2 + 1)))

def expectedLayout (width : Nat) : Configuration.Layout :=
  ⟨⟨width, 1⟩, ⟨0, 3 * width + 2⟩⟩

def check : Bool :=
  (List.range 5).all (fun width =>
    (allBits width).all (fun message =>
      let results := paths (61 * width + 40) (Configuration.initial message)
      decide (results.length = 2 ^ width) &&
        results.all (fun result => result.1.halted &&
          decide (result.1.layout = expectedLayout width) &&
          decide (result.2 = 61 * width + 40))))

#eval do
  if check then
    IO.println "Encryption layout check passed: widths 0–4, all plaintexts and random branches."
  else
    throw (IO.userError "Encryption layout check failed.")

end Foundation.Examples.GeneratedEncryptionLayoutCheck
