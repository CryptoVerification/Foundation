import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyRepeatedCallback

namespace Foundation.Symmetric.EncryptThenMAC.RepeatedCallbackExamples
open Machine PrivacyMachine

-- Empty and nonempty stores retain the same one blank to the left. The
-- prewritten private response header remains ahead of the copied key.
#guard [[], [false], [true, false, true, true]].all fun bits =>
  let before := [some false]
  let (final, used) := Masking.simulate (.native PrivateKeyCopy.code) false (8 * bits.length + 5)
    (.running (RetainedResponse.copying [] bits before))
  match final with
  | .running machine => machine == PrivateKeyCopy.finish bits before && used == 8 * bits.length + 5
  | _ => false

def code : Source.Code :=
  [.native (.write .output false), .native (.moveRight .output),
   .native (.write .output true), .native (.moveLeft .output),
   .call, .call, .call, .call, .native .halt]

def oracle (state : Nat) (_ : List Bool) : Nat × List Bool :=
  (state + 1, if state == 0 then [true, true] else [false])

-- The actual source makes four adaptive calls: each new request is its
-- previous authenticated response. There is one private generation phase.
#guard [false, true].all fun coin =>
  let (frame, used) := simulate code oracle coin 2000 (initial 0 [true, true, true, true] [])
  let firstResponse := [true, true, coin, coin]
  let expectedKey : TableMAC.Key 2 := (fun _ => coin, fun _ => coin)
  match frame.control with
  | .source key _ =>
      terminal frame.control && publicPacket frame.control == some [false] && frame.state == 4 &&
      key == ResponseHandoff.retainedKey expectedKey && key.left == [none] &&
      frame.sourceTrace.reverse == [([false, true], firstResponse), (firstResponse, [false]),
        ([false], [false]), ([false], [false])] &&
      frame.externalTrace.reverse == [([false, true], [true, true]), (firstResponse, [false]),
        ([false], [false]), ([false], [false])] &&
      (simulate code oracle coin 5000 (initial 0 [true, true, true, true] [])).2 == used
  | _ => false

-- All endpoint states, for either store layout and every tag/key choice,
-- carry the exact same retained key and source-frame state.
example {State : Type*} {width : Nat} (oracle : CryptoOracle.Interactive.BitOracle State)
    (machine : Configuration) (request : List Bool) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool))
    (layout : StoreLayout) (key : TableMAC.Key width) (ciphertext : Option Bool) :
    (storedCallback code oracle machine request state sourceTrace externalTrace layout key ciphertext).outcome.map Prod.fst =
      PMF.pure (callbackResult machine request state sourceTrace externalTrace
        (ResponseHandoff.retainedKey key) key ciphertext) :=
  storedCallback_result_distribution code oracle machine request state sourceTrace externalTrace layout key ciphertext

end Foundation.Symmetric.EncryptThenMAC.RepeatedCallbackExamples
