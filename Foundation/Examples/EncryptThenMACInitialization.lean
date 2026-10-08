import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyInitialization

namespace Foundation.Symmetric.EncryptThenMAC.InitializationExamples
open Machine PrivacyMachine

def haltCode : Source.Code := [.native .halt]
def oracle (state : Nat) (_ : List Bool) : Nat × List Bool := (state + 1, [])
def start : Frame Nat := ⟨37,
  .initializing (.running (Configuration.initial [false, true]))
    (PrivateKeyGeneration.initial [true, true, true, true]),
  [([false], [true])], [([true], [false])]⟩

-- After all 28 generator transitions, the private ready store is still
-- owned by initialization. No instruction of the source has run.
#guard [false, true].all fun coin =>
  let (frame, used) := simulate haltCode oracle coin 28 start
  match frame.control with
  | .initializing (.running source) (.ready key) =>
      used == 28 && source == Configuration.initial [false, true] &&
      key.bits == List.replicate 4 coin && frame.state == 37 &&
      frame.sourceTrace == start.sourceTrace && frame.externalTrace == start.externalTrace
  | _ => false

-- The 29th transition transfers this same store. The 30th executes halt.
#guard [false, true].all fun coin =>
  let (frame, used) := simulate haltCode oracle coin 29 start
  match frame.control with
  | .source key (.running source) =>
      used == 29 && source == Configuration.initial [false, true] &&
      key.bits == List.replicate 4 coin && frame.state == 37 &&
      frame.sourceTrace == start.sourceTrace && frame.externalTrace == start.externalTrace
  | _ => false

#guard [false, true].all fun coin =>
  let (frame, used) := simulate haltCode oracle coin 100 start
  terminal frame.control && used == 30 && frame.state == 37 &&
    frame.sourceTrace == start.sourceTrace && frame.externalTrace == start.externalTrace

-- The prefix claim is universal over the probability distribution, not
-- just the two fixed-coin execution checks above.
example (fuel : Nat) (hFuel : fuel ≤ 28) (frame : Frame Nat)
    (hFrame : frame ∈ (eval haltCode (fun state _ => PMF.pure (state + 1, [])) fuel start).support) :
    Timing.sourceBoundary frame = false := by
  exact initialization_before_source haltCode _ (fun _ => 2) 0 fuel _ 37 _ _ hFuel frame hFrame

end Foundation.Symmetric.EncryptThenMAC.InitializationExamples
