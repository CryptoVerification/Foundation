import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityCallback
import Foundation.Constructions.Symmetric.EncryptThenMAC.TableMAC

namespace Foundation.Symmetric.EncryptThenMAC.IntegrityCallbackExamples
open Machine Foundation.Probability IntegrityMachine

noncomputable def oracle {width : Nat} (macKey : TableMAC.Key width) (_ : Unit) (ciphertext : Bool) :
    PMF (Unit × List Bool) := PMF.pure ((), (TableMAC.sign macKey ciphertext).toList)

theorem tag_length {width : Nat} (macKey : TableMAC.Key width) (ciphertext : Bool)
    (answer : Unit × List Bool) (h : answer ∈ (oracle macKey () ciphertext).support) :
    answer.2.length = width := by
  simp only [oracle, PMF.mem_support_pure_iff] at h
  subst answer
  simp

-- Instantiate the generic capability-length contract from the actual MAC,
-- for every authentication key, pending source configuration and history.
example {width : Nat} (macKey : TableMAC.Key width) (encKey used : Bool)
    (code : SourceCode) (machine : Configuration) (request : List Bool)
    (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool)) :
    eval code (oracle macKey) (queryBudget used width + 1)
      ⟨(), .source encKey used (.awaiting machine request), sourceTrace, signingTrace⟩ =
      queryResult used encKey machine request () sourceTrace signingTrace (oracle macKey) :=
  awaiting_query_run code (oracle macKey) encKey machine request () sourceTrace signingTrace used width
    (fun answer h => tag_length macKey _ answer h)

def testOracle (count : Nat) (ciphertext : Bool) : Nat × List Bool :=
  (count + 1, [!ciphertext, ciphertext])

-- Source resumption and its real loader continue after the request boundary.
#guard [false, true].all fun key => [false, true].all fun exhausted =>
  let source := Configuration.initial [true]
  let start : Frame Nat := ⟨0, .source key exhausted (.awaiting source [false]), [], []⟩
  let (final, used) := simulate [.native .halt] testOracle false 1000 start
  terminal final.control && final.state == (if exhausted then 0 else 1) &&
    final.signingTrace == (if exhausted then [] else [(key, [!key, key])]) &&
    publicPacket final.control == some (if exhausted then [false] else [true, key, !key, key]) &&
    used == (if exhausted then 28 else 61)

end Foundation.Symmetric.EncryptThenMAC.IntegrityCallbackExamples
