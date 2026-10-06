import Foundation.Crypto.Semantics.Machine.ReifyCompactProgram

namespace Machine.CompactProgram.Examples

private def smallSource : Program :=
  (List.replicate 3 (.jump 2)).map (Instruction.asSubroutine 4 9 3) ++ [.halt]

private def smallCode : Program :=
  Program.withSubroutine [.halt] (GuardedCompiler.compile smallSource) [.halt] 300

private def smallView : CompactProgram smallCode := by compact_program

/- Compare every instruction, including the first out-of-bounds address, with
the original executable compiler. This exercises map, replication, append,
guarded blocks, and relocation together. -/
/-- info: true -/
#guard_msgs in
#eval
  let expected := smallCode
  smallView.length == expected.length &&
    (List.range (expected.length + 2)).all fun pc =>
      smallView.lookup pc == expected[pc]?

private def largeView : CompactProgram
    (GuardedCompiler.compile
      (GuardedCompiler.compile (List.replicate 1000000 .halt))) := by
  compact_program

/- More than four billion instructions, without materializing either layer.
Check a middle block, the last instruction, and the fall-off boundary. -/
/-- info: true -/
#guard_msgs in
#eval
  largeView.length == 4624000069 &&
    largeView.lookup 2312000000 == some .halt &&
    largeView.lookup (largeView.length - 1) == some .halt &&
    largeView.lookup largeView.length == none

end Machine.CompactProgram.Examples
