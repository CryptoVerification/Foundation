import Foundation.Crypto.Semantics.Oracle.FreshMaskAdaptiveFirstHalt

/-! Public final caller control and actual first-halt time reveal no
plaintext after at least one fresh-key masking call. Full request traces
are intentionally not included in this observation: they contain plaintext.
This is an execution-level theorem, before security-class registration. -/
namespace CryptoOracle.Interactive.FreshMaskAdaptiveExecution
open Machine Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false

/-- Reindex a raw request by a proved public width without changing execution. -/
theorem law_succ_of_width {State : Type u} (rounds : Nat) (state : State)
    (past : List (Option Bool)) (request : List Bool) (trace : List (List Bool × List Bool))
    (width : Nat) (hWidth : request.length = width) :
    law (rounds + 1) state past request trace =
      (uniform (Bits width)).bind (fun ciphertext =>
        law rounds state (some true :: past) ciphertext.toList ((request, ciphertext.toList) :: trace)) := by
  subst width
  rfl

theorem law_control_trace_independence {State : Type u} (rounds : Nat) (state : State)
    (past : List (Option Bool)) (request : List Bool)
    (leftTrace rightTrace : List (List Bool × List Bool)) :
    (law rounds state past request leftTrace).map Configuration.control =
    (law rounds state past request rightTrace).map Configuration.control := by
  induction rounds generalizing past request leftTrace rightTrace with
  | zero => simp [law, PMF.pure_map, AdaptiveBitstringLoop.finished]
  | succ rounds ih =>
      rw [law, law, PMF.map_bind, PMF.map_bind]
      congr 1
      funext ciphertext
      exact ih (some true :: past) ciphertext.toList
        ((request, ciphertext.toList) :: leftTrace) ((request, ciphertext.toList) :: rightTrace)

/-- At least one call is essential; zero calls retain the original message. -/
theorem law_control_plaintext_independence {State : Type u} (rounds : Nat) (state : State)
    (past : List (Option Bool)) {width : Nat} (left right : Bits width)
    (leftTrace rightTrace : List (List Bool × List Bool)) :
    (law (rounds + 1) state past left.toList leftTrace).map Configuration.control =
    (law (rounds + 1) state past right.toList rightTrace).map Configuration.control := by
  rw [law_succ_of_width rounds state past left.toList leftTrace width (Bits.length_toList left),
    law_succ_of_width rounds state past right.toList rightTrace width (Bits.length_toList right),
    PMF.map_bind, PMF.map_bind]
  congr 1
  funext ciphertext
  exact law_control_trace_independence rounds state (some true :: past) ciphertext.toList
    ((left.toList, ciphertext.toList) :: leftTrace) ((right.toList, ciphertext.toList) :: rightTrace)

def publicControl {State : Type u} :
    PacketResponseSource.Control NativePacketService.Control State Unit → CryptoOracle.Interactive.Control
  | .source _ frame => frame.control
  | _ => .finished false

variable {State : Type u} (oracle : BitOracle State)

/-- Arbitrary probabilistic observations of final physical caller control
and actual elapsed time have the same law for equal-width plaintexts. -/
theorem first_halt_public_perfect_secrecy (rounds : Nat) (state : State) (past : List (Option Bool))
    {width : Nat} (left right : Bits width) (leftTrace rightTrace : List (List Bool × List Bool))
    {Observed : Type*} (observer : CryptoOracle.Interactive.Control × Nat → PMF Observed) :
    ((runToBoundary (FreshMaskAdaptiveRound.runtime oracle).step PacketResponseSource.terminal
      (timeBound (rounds + 1) width)
      ((FreshMaskAdaptiveRound.runtime oracle).embed ()
        (AdaptiveBitstringLoop.frame state (rounds + 1) past left.toList leftTrace))).map
          (fun result => (publicControl result.1, result.2))).bind observer =
    ((runToBoundary (FreshMaskAdaptiveRound.runtime oracle).step PacketResponseSource.terminal
      (timeBound (rounds + 1) width)
      ((FreshMaskAdaptiveRound.runtime oracle).embed ()
        (AdaptiveBitstringLoop.frame state (rounds + 1) past right.toList rightTrace))).map
          (fun result => (publicControl result.1, result.2))).bind observer := by
  have hl := first_halt_joint oracle (rounds + 1) state past left.toList leftTrace
  have hr := first_halt_joint oracle (rounds + 1) state past right.toList rightTrace
  rw [Bits.length_toList] at hl hr
  rw [hl, hr, PMF.map_comp, PMF.map_comp]
  have h := congrArg (fun distribution =>
    (distribution.map (fun control => (control, timeBound (rounds + 1) width))).bind observer)
    (law_control_plaintext_independence rounds state past left right leftTrace rightTrace)
  simpa only [PMF.map_comp, Function.comp_def, publicControl, FreshMaskAdaptiveRound.runtime,
    CallerRuntime.packet] using h

end CryptoOracle.Interactive.FreshMaskAdaptiveExecution
