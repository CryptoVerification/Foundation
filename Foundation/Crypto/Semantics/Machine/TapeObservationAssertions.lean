import Foundation.Crypto.Semantics.Machine.ProgramAssertions
import Foundation.Crypto.Semantics.Machine.TapeReading

/-! Syntactic certificates for preserving a tape's bit observation. Moving
the head is allowed and still costs native steps. Writes, erases and random
writes on the selected tape are rejected. Other tapes are unrestricted. -/
namespace Machine
open Foundation.Probability

def Instruction.preservesBits (which : TapeId) : Instruction → Prop
  | .write tape _ | .erase tape | .randomBit tape => tape ≠ which
  | _ => True

instance (which : TapeId) (instruction : Instruction) :
    Decidable (instruction.preservesBits which) := by
  cases instruction <;> simp only [Instruction.preservesBits] <;> infer_instance

theorem Instruction.bits_precondition (instruction : Instruction) (which : TapeId)
    (h : instruction.preservesBits which) (start : Configuration) :
    instruction.precondition (fun target => (target.tape which).bits = (start.tape which).bits) start := by
  cases instruction <;> cases which <;>
    simp_all [preservesBits, Instruction.precondition, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance]
  all_goals split <;> simp_all

def Program.preservesBits (code : Program) (which : TapeId) : Prop :=
  ∀ pc : Fin code.length, (code[pc.val]).preservesBits which

instance (code : Program) (which : TapeId) : Decidable (code.preservesBits which) :=
  inferInstanceAs (Decidable (∀ pc : Fin code.length, (code[pc.val]).preservesBits which))

namespace TapeObservationAssertions

def assertions (which : TapeId) (bits : List Bool) : Program.Assertions where
  active _ input output := (({inputTape := input, outputTape := output} : Configuration).tape which).bits = bits
  stopped _ input output := (({inputTape := input, outputTape := output} : Configuration).tape which).bits = bits

theorem holds (which : TapeId) (bits : List Bool) (machine : Configuration) :
    (assertions which bits).Holds machine ↔ (machine.tape which).bits = bits := by
  cases which <;> cases hh : machine.halted <;>
    simp [assertions, Program.Assertions.Holds, hh, Configuration.tape]

theorem verified (code : Program) (which : TapeId) (hCode : code.preservesBits which)
    (bits : List Bool) : (assertions which bits).Verified code := by
  constructor
  · intro pc start hPc hActive hAssertion
    apply (Instruction.precondition_iff (by rw [hPc]; exact List.getElem?_eq_getElem pc.isLt) hActive).mpr
    intro target hStep
    apply (holds which bits target).mpr
    have hBits := Instruction.precondition_step
      (by rw [hPc]; exact List.getElem?_eq_getElem pc.isLt) hActive hStep
      (Instruction.bits_precondition code[pc.val] which (hCode pc) start)
    rw [hBits]
    cases which <;> exact hAssertion
  · intro pc input output _ h
    exact h

theorem preserved_prefix (code : Program) (which : TapeId) (hCode : code.preservesBits which)
    (start target : Configuration) (elapsed : Nat)
    (hTarget : target ∈ (evalConfigWithin code start elapsed).support) :
    (target.tape which).bits = (start.tape which).bits :=
  (holds which _ target).mp ((verified code which hCode _).prefix start target
    ((holds which _ start).mpr rfl) elapsed hTarget)

end TapeObservationAssertions
end Machine
