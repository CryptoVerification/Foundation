import Foundation.Constructions.Symmetric.PRGPolygraph
import Foundation.Crypto.Logic.Polygraph.Translation
import Foundation.Examples.PRGEncryption

/-! Execute the local-rule PRG diagram without interpreting security, then
connect the same emitted programs to the existing finite masking machine. -/
namespace Foundation.Symmetric.PolygraphExamples

open Machine CryptoLogic.General CryptoLogic.General.Backends
open Generator
set_option backward.isDefEq.respectTransparency false

def programs (output : List (Nat × Sigma system.Code)) : List (Nat × Masking.Code) :=
  output.filterMap fun (i, code) => match code with
    | ⟨.masking, program⟩ => some (i, program)
    | _ => none

/-- info: true -/
#guard_msgs in
#eval programs (CryptoLogic.Polygraph.Derivation.run Polygraph.proof Examples.testProgram) ==
  [(0, .masked false Examples.testProgram), (0, .masked true Examples.testProgram)]

/-- info: [0, 0] -/
#guard_msgs in
#eval Polygraph.proof.occurrences.map Fin.val

/-- info: [(some false, 43), (some true, 43)] -/
#guard_msgs in
#eval (programs (CryptoLogic.Polygraph.Derivation.run Polygraph.proof Examples.testProgram)).map
  fun (_, code) =>
    let (finish, used) := Masking.simulate code false
      (Examples.testGenerator.reductionTime (fun _ => 14) 0)
      (Masking.initial code Examples.testHeader [false, false] [true, false] [false, true])
    (Masking.result finish, used)

/-- info: [(none, 42), (none, 42)] -/
#guard_msgs in
#eval (programs (CryptoLogic.Polygraph.Derivation.run Polygraph.proof Examples.testProgram)).map
  fun (_, code) =>
    let (finish, used) := Masking.simulate code false
      (Examples.testGenerator.reductionTime (fun _ => 14) 0 - 1)
      (Masking.initial code Examples.testHeader [false, false] [true, false] [false, true])
    (Masking.result finish, used)

-- Direct code interpretation agrees with reconstruction on this local proof.
example : Polygraph.proof.eval
    (CryptoLogic.Presented.codeModel Polygraph.parameters Polygraph.context.length)
    (fun i code => [(i, ⟨Polygraph.language.machine (Polygraph.context.claim i).object, code⟩)]) 0 =
    (CryptoLogic.Polygraph.Derivation.plan Polygraph.proof).run :=
  CryptoLogic.Polygraph.Derivation.code_eval Polygraph.proof

end Foundation.Symmetric.PolygraphExamples
