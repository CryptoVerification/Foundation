import Foundation.Constructions.Symmetric.EncryptThenMAC.Translation
import Foundation.Examples.MachineProgramTransformation
import Foundation.Crypto.Logic.General.Backends

/-! Executable tests of the EtM rule's code interpretation. These check
finite compiler branching, not a realization of an encryption or MAC scheme. -/
namespace Foundation.Symmetric.EncryptThenMAC.TranslationExamples

open CryptoLogic.General CryptoLogic.General.Backends Machine Machine.Examples
open Operational
set_option backward.isDefEq.respectTransparency false

-- Distinct nonidentity native compilers make exchanged outputs observable.
def encryptionCompiler : Compiler system .native .native :=
  .primitive (.native (.suffix [.halt]))

def macCompiler : Compiler system .native .native :=
  .primitive (.native constantAnswerCompiler)

def emitted (p : Machine.Program) :=
  (Operational.plan encryptionCompiler macCompiler
    (Γ := Logic.context.map (U := Logic.lower) id) (Logic.expansion.translate Logic.proof)).run p

-- Compare computable syntax indices: Program.encode materializes a unary
-- list whose length is this index, which is unnecessary for equality.
/-- info: true -/
#guard_msgs in
#eval (emitted randomOutputBit).map (fun out => (out.1.val, match out.2 with
      | ⟨.native, p⟩ => @Encodable.encode Machine.Program inferInstance p
      | _ => 0)) ==
    [(0, Encodable.encode (randomOutputBit ++ [.halt])), (1, Encodable.encode haltImmediately)]

example (p : Machine.Program) : emitted p =
    [(0, ⟨Kind.native, p ++ [.halt]⟩), (1, ⟨Kind.native, haltImmediately⟩)] :=
  proof_plan encryptionCompiler macCompiler p

example : encryptionCompiler.run randomOutputBit ≠ macCompiler.run randomOutputBit := by
  change (randomOutputBit ++ [.halt] : Machine.Program) ≠ haltImmediately
  decide

-- The two branches need different numbers of actual native transitions.
-- These facts only validate the fixture programs, not scheme implementations.
example : HaltsWithin (macCompiler.run randomOutputBit) [] 1 := by
  exact haltImmediately_haltsWithin []

example : HaltsWithin (encryptionCompiler.run randomOutputBit) [] 2 := by
  exact (haltsWithin_append_halt_iff randomOutputBit [] 2).2 randomOutputBit_haltsWithin

end Foundation.Symmetric.EncryptThenMAC.TranslationExamples
