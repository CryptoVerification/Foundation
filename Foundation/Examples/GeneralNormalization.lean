import Foundation.Crypto.Meta.General.Normalization
import Foundation.Examples.GeneralResources

namespace CryptoLogic.General.NormalizationExamples

open Backends Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

def nodes {m n} : Compiler system m n → Nat
  | .identity _ => 1
  | .primitive _ => 1
  | .comp first second => 1 + nodes first + nodes second

/-- Left-associated composition and identities on both sides of a machine
change normalize into the same ordered two-primitive chain. -/
def redundant : Compiler system Kind.native Kind.masking :=
  .comp
    (.comp (.identity _) (.primitive (.native (.suffix [.halt]))))
    (.comp (.identity _) (.comp (.primitive (.mask true)) (.identity _)))

example : redundant.normalize =
    .comp (.primitive (.native (.suffix [.halt]))) (.primitive (.mask true)) := rfl

/-- info: (9, 3, 2) -/
#guard_msgs in
#eval (nodes redundant, nodes redundant.normalize, redundant.chain.length)

/-- info: true -/
#guard_msgs in
#eval
  let output : Machine.Masking.Code := redundant.normalize.run [.randomBit .output, .halt]
  output == .masked true [.randomBit .output, .halt, .halt]

-- Binary contraction still returns two codes for the same assumption.
/-- info: true -/
#guard_msgs in
#eval
  Foundation.Symmetric.LogicExamples.programs
    ((Generator.Logic.sharedDerivation Foundation.Symmetric.LogicExamples.G
      Foundation.Symmetric.LogicExamples.time Foundation.Symmetric.LogicExamples.family).normalize.run
      Foundation.Symmetric.Examples.testProgram) ==
    [(0, .masked false Foundation.Symmetric.Examples.testProgram),
     (0, .masked true Foundation.Symmetric.Examples.testProgram)]

-- The terminal identity is removed from each PRG compiler, not from the
-- target machine's own instruction code.
/-- info: ([3, 3], [1, 1]) -/
#guard_msgs in
#eval
  let d := Generator.Logic.sharedDerivation Foundation.Symmetric.LogicExamples.G
    Foundation.Symmetric.LogicExamples.time Foundation.Symmetric.LogicExamples.family
  (d.compilers.map (fun (_, ⟨_, c⟩) => nodes c),
    d.normalize.compilers.map (fun (_, ⟨_, c⟩) => nodes c))

-- Interactive compilation is supported by the same normalizer.
/-- info: true -/
#guard_msgs in
#eval (Examples.oracle.normalize.run CryptoOracle.Examples.adaptiveCode).map
    (fun (i, c) => (i, Examples.summary c)) == [(0, Kind.interactive, false, 4)]

-- Proofs cover arbitrary source programs, not only the execution fixtures.
example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (p : Machine.Program) :
    (Generator.Logic.sharedDerivation G t F).normalize.run p =
      (Generator.Logic.sharedDerivation G t F).run p :=
  Derivation.normalize_run (Generator.Logic.sharedDerivation G t F) p

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal) :
    (Generator.Logic.sharedAnalysis G t F).normalize.loss =
      (Generator.Logic.sharedAnalysis G t F).loss := Derivation.Analysis.normalize_loss _

-- Equality of whole witness records retains the precise resource values,
-- stopping proof, distribution equality, and target admissibility evidence.
example (G : Generator) (F : InstanceFamily G.encryptionGoal) :
    (Generator.Logic.sharedAnalysis G (fun _ => 2) F).normalize.runWitnesses _
      (ResourceExamples.prgWitness G F) =
    (Generator.Logic.sharedAnalysis G (fun _ => 2) F).runWitnesses _
      (ResourceExamples.prgWitness G F) := Derivation.Analysis.normalize_runWitnesses _ _ _

example : Examples.oracle.normalize.runWitnesses _ Examples.oracleWitness =
    Examples.oracle.runWitnesses _ Examples.oracleWitness := Derivation.normalize_runWitnesses _ _ _

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal) :
    (Generator.Logic.sharedDerivation G t F).normalize.normalize =
      (Generator.Logic.sharedDerivation G t F).normalize := Derivation.normalize_idempotent _

end CryptoLogic.General.NormalizationExamples
