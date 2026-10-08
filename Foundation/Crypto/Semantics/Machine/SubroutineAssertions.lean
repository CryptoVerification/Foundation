import Foundation.Crypto.Semantics.Machine.ProgramAssertions
import Foundation.Crypto.Semantics.Machine.ClosedSubroutineProbability

/-! Carry verified source assertions through actual native embedding.
The statement covers the callee until its first return (then boundary padding),
not execution of the caller after return. It preserves the complete physical
configuration and needs no stopping bound on the source program. -/
namespace Machine.Program.Assertions
open Foundation.Probability

/-- The actual embedded prefix is a relocated, assertion-satisfying source
state, or the active return corresponding to a halted source state. -/
theorem Verified.subroutine_prefix {assertions : Program.Assertions} {source : Program}
    (verified : assertions.Verified source) (pre suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc < source.length → pre.length + pc ≠ returnPc)
    (hClosed : ∀ start target, start.pc < source.length → Step source start target →
      target.halted = false → target.pc < source.length)
    (start : Configuration) (hPc : start.pc < source.length) (hActive : start.halted = false)
    (hStart : assertions.Holds start) (elapsed : Nat) (target : Configuration)
    (hTarget : target ∈ (evalReturnWithin (Program.withSubroutine pre source suffix returnPc)
      returnPc (start.rebasePc pre.length) elapsed).support) :
    ∃ sourceState, assertions.Holds sourceState ∧
      target = if sourceState.halted then sourceState.resumeAt returnPc else sourceState.rebasePc pre.length := by
  rw [Program.evalReturnWithin_configuration_eq_of_closed pre source suffix returnPc
    hLayout hClosed start hPc hActive elapsed, PMF.mem_support_map_iff] at hTarget
  obtain ⟨sourceState, hs, he⟩ := hTarget
  exact ⟨sourceState, verified.prefix start sourceState hStart elapsed hs, he.symm⟩

/-- Any assertion consequence concerning the two full tapes survives code
relocation and conversion of a halt into an active return. -/
theorem Verified.subroutine_tapes {assertions : Program.Assertions} {source : Program}
    (verified : assertions.Verified source) (pre suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc < source.length → pre.length + pc ≠ returnPc)
    (hClosed : ∀ start target, start.pc < source.length → Step source start target →
      target.halted = false → target.pc < source.length)
    (property : Tape → Tape → Prop)
    (hConsequence : ∀ sourceState, assertions.Holds sourceState → property sourceState.inputTape sourceState.outputTape)
    (start : Configuration) (hPc : start.pc < source.length) (hActive : start.halted = false)
    (hStart : assertions.Holds start) (elapsed : Nat) (target : Configuration)
    (hTarget : target ∈ (evalReturnWithin (Program.withSubroutine pre source suffix returnPc)
      returnPc (start.rebasePc pre.length) elapsed).support) :
    property target.inputTape target.outputTape := by
  obtain ⟨sourceState, hs, he⟩ := verified.subroutine_prefix pre suffix returnPc hLayout hClosed
    start hPc hActive hStart elapsed target hTarget
  rw [he]
  cases hh : sourceState.halted <;>
    simpa only [hh, Bool.false_eq_true, ↓reduceIte, Configuration.resumeAt,
      Configuration.rebasePc] using hConsequence sourceState hs

end Machine.Program.Assertions
