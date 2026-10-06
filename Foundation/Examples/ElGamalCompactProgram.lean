import Foundation.Constructions.ElGamal.PrimeOrderCompactCode

namespace ElGamal.PrimeOrderRepresentation.CompactExamples

open Machine

/- Exact size evaluation of the full concrete compiler, including both fixed
subroutines. None of these tests materializes the instruction lists. -/
/-- info: true -/
#guard_msgs in
#eval
  compactNormalizer.length == 2171977742 &&
    compactMultiplier.length == 78615 &&
    compactEmptyCode.length == 147699834040 &&
    compactEmptyCode.lookup 0 == some (.branch .input 5 1 3) &&
    compactEmptyCode.lookup (compactEmptyCode.length - 1) == some .halt &&
    compactEmptyCode.lookup compactEmptyCode.length == none

/- The public compiler also accepts a supplied source view: source growth must
be accounted for without expanding either fixed subroutine. -/
private def oneInstruction : CompactProgram [.halt] := by compact_program

/-- info: true -/
#guard_msgs in
#eval
  let compiled := compactCompile oneInstruction
  compiled.length == 147699834176 &&
    compiled.lookup (compiled.length - 1) == some .halt &&
    compiled.lookup (compiled.length + 1) == none

/- Fetch and execute an actual transition from the full concrete output. The
all-configuration equality with Machine.next is CompactProgram.next_eq. -/
/-- info: true -/
#guard_msgs in
#eval
  match compactEmptyCode.next (Configuration.initial []) with
  | some (.inl c) => c.pc == 5 && !c.halted
  | _ => false

end ElGamal.PrimeOrderRepresentation.CompactExamples
