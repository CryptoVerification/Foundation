import Foundation.Constructions.Symmetric.PRGOptimizedPolygraph
import Foundation.Constructions.Symmetric.PRGOptimizedPipeline
import Foundation.Examples.PRGEncryption

/-! Execute the two codes emitted by the actual local PRG proof. The fixture
is intentionally insecure and supplies no security premise. General theorems
hold for arbitrary generators, programs, messages and native random branches. -/
namespace Foundation.Symmetric.Generator.Optimized.Examples
open Machine
set_option backward.isDefEq.respectTransparency false

abbrev testGenerator := Foundation.Symmetric.Examples.testGenerator
abbrev testProgram := Foundation.Symmetric.Examples.testProgram
abbrev testHeader := Foundation.Symmetric.Examples.testHeader

def programs (output : List (Nat × Sigma system.Code)) : List (Mode × Masking.Code) :=
  output.filterMap fun (_, code) => match code with
    | ⟨true, code⟩ => some code
    | ⟨false, _⟩ => none

def simulate (code : Mode × Masking.Code) (fuel : Nat) : Option Bool × Nat :=
  let start := Masking.initial code.2 testHeader [false, false] [true, false] [false, true]
  let (finish, used) := match code.1 with
    | .original => Masking.simulate code.2 false fuel start
    | .fused => Masking.Fused.simulate code.2 false fuel start
  (Masking.result finish, used)

/-- info: [(some false, 42), (some true, 42)] -/
#guard_msgs in
#eval (programs (CryptoLogic.Polygraph.Derivation.run Polygraph.proof testProgram)).map
  (fun code => simulate code 42)

/-- info: [(none, 41), (none, 41)] -/
#guard_msgs in
#eval (programs (CryptoLogic.Polygraph.Derivation.run Polygraph.proof testProgram)).map
  (fun code => simulate code 41)

/-- info: [(some false, 43), (some true, 43)] -/
#guard_msgs in
#eval [simulate (.original, .masked false testProgram) 43,
  simulate (.original, .masked true testProgram) 43]

example : time testGenerator (fun _ => 14) 0 = 42 := rfl
example : testGenerator.reductionTime (fun _ => 14) 0 = 43 := rfl

/-- No comparison between different physical resource units is needed:
both outputs use the explicitly defined controller transition budget. -/
example : ∀ n, time testGenerator (fun _ => 14) n < testGenerator.reductionTime (fun _ => 14) n :=
  time_strict _ _

-- With completely empty input there is no last loaded cell to fuse.
-- Both evaluators keep the old dispatch, as required by the theorem's
-- explicit nonempty-input premise (the actual PRG header is never empty).
/-- info: (4, 4) -/
#guard_msgs in
#eval
  let code := Masking.Code.masked false [.halt]
  let start := Masking.initial code [] [] [] []
  ((Masking.simulate code false 10 start).2, (Masking.Fused.simulate code false 10 start).2)

/-- info: [((some false, 42), 100), ((some true, 42), 100)] -/
#guard_msgs in
#eval (programs (CryptoLogic.Polygraph.Derivation.run Polygraph.proof testProgram)).map fun code =>
  let expanded := (Pipeline.compiler 100).run code
  (simulate expanded 42, expanded.2.program.length - code.2.program.length)

end Foundation.Symmetric.Generator.Optimized.Examples
