import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyCallback

namespace Foundation.Symmetric.EncryptThenMAC.CallbackExamples
open Machine PrivacyMachine

def key : TableMAC.Key 2 := (fun i => i.val == 0, fun i => i.val == 1)
def machine : Configuration := { pc := 0, inputTape := Tape.ofBits [false, true] }
def code : Source.Code := [.native .halt]
def oracle (state : Nat) (_ : List Bool) : Nat × List Bool := (state + 1, [])
def start (ciphertext : Option Bool) : Frame Nat :=
  embedResponder machine [false, true] 17 [([true], [false])] [([false], [true])]
    (GeneratedResponse.initial key ciphertext)

def atResume (ciphertext : Option Bool) (fuel : Nat) : Bool :=
  let (frame, used) := simulate code oracle false fuel (start ciphertext)
  let expected := callbackResult machine [false, true] 17 [([true], [false])] [([false], [true])]
    (ResponseHandoff.retainedKey key) key ciphertext
  (frame.state, frame.control, frame.sourceTrace, frame.externalTrace) ==
    (expected.state, expected.control, expected.sourceTrace, expected.externalTrace) && used == fuel

-- Success takes the full 96 transitions. Failure resumes in only 56,
-- below its upper bound of 83: unused time must continue source execution.
#guard atResume (some true) 96
#guard !atResume (some true) 95
#guard atResume none 56
#guard !atResume none 55
#guard !atResume none 83
#guard
  let (frame, _) := simulate code oracle false 83 (start none)
  terminal frame.control && frame.state == 17 &&
    frame.sourceTrace == [([false, true], [false]), ([true], [false])] &&
    frame.externalTrace == [([false], [true])]

def statefulOracle (state : Nat) (_ : List Bool) : Nat × List Bool :=
  (state + 1, if state == 17 then [true, true] else [false])

#guard
  let initial : Frame Nat := ⟨17, .source (PrivateKeyGeneration.store key) (.awaiting machine [false, true]),
    [([true], [false])], [([false], [true])]⟩
  let (frame, used) := simulate code statefulOracle false 97 initial
  let expected := callbackResult machine [false, true] 18 [([true], [false])]
    [([false, true], [true, true]), ([false], [true])] (ResponseHandoff.retainedKey key) key (some true)
  used == 97 && (frame.state, frame.control, frame.sourceTrace, frame.externalTrace) ==
    (expected.state, expected.control, expected.sourceTrace, expected.externalTrace)

#guard
  let initial : Frame Nat := ⟨18, .source (PrivateKeyGeneration.store key) (.awaiting machine [false, true]),
    [([true], [false])], [([false], [true])]⟩
  let (frame, used) := simulate code statefulOracle false 57 initial
  let expected := callbackResult machine [false, true] 19 [([true], [false])]
    [([false, true], [false]), ([false], [true])] (ResponseHandoff.retainedKey key) key none
  used == 57 && (frame.state, frame.control, frame.sourceTrace, frame.externalTrace) ==
    (expected.state, expected.control, expected.sourceTrace, expected.externalTrace)

example (ciphertext : Option Bool) (result : Frame Nat × Nat)
    (h : result ∈ (generatedCallback code (fun state _ => PMF.pure (state + 1, []))
      machine [false, true] 17 [([true], [false])] [([false], [true])] key ciphertext).outcome.support) :
    result.2 ≤ 96 :=
  generatedCallback_bounded code _ machine [false, true] 17 _ _ key ciphertext result h

end Foundation.Symmetric.EncryptThenMAC.CallbackExamples
