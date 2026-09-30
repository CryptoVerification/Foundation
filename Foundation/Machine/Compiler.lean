import Foundation.Machine.Subroutine

namespace Machine

/-- A small finite syntax of program-code constructions. Every constructor
has a structurally recursive executable interpreter. Semantic correctness
of a particular construction remains a separate proof obligation. -/
inductive ProgramCompiler where
  | identity
  | constant (code : Program)
  | prefix (code : Program)
  | suffix (code : Program)
  | twoCalls (pre middle post : Program)
  | comp (first second : ProgramCompiler)
  deriving Repr, Encodable

namespace ProgramCompiler

def run : ProgramCompiler → Program → Program
  | .identity, source => source
  | .constant code, _ => code
  | .prefix code, source => code ++ source
  | .suffix code, source => source ++ code
  | .twoCalls pre middle post, source =>
      Program.withTwoSubroutines pre middle post source
  | .comp first second, source => second.run (first.run source)

/-- This constructor emits two rebased source blocks. It supplies finite
code construction, while protocol correctness and runtime remain separate
proof obligations. -/
@[simp] theorem run_twoCalls (pre middle post source : Program) :
    (twoCalls pre middle post).run source =
      Program.withTwoSubroutines pre middle post source := rfl

/-- A finite bitstring-to-bitstring compiler. Invalid source codes are
rejected; valid source codes yield the encoding of the transformed program. -/
def runCode (C : ProgramCompiler) (bits : List Bool) : Option (List Bool) :=
  (Program.decode bits).map (fun p => Program.encode (C.run p))

@[simp] theorem runCode_encode (C : ProgramCompiler) (p : Program) :
    C.runCode (Program.encode p) = some (Program.encode (C.run p)) := by
  simp [runCode]

end ProgramCompiler

end Machine
