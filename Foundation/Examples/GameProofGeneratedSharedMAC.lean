import Foundation.Crypto.Logic.Polygraph.GameProofShared
import Foundation.Examples.GameProofMACNormalization

/-! Compile the actual terminalCoherence output of the retained-state MAC
example. No hand-written repetition family is substituted for the generator.
All boundary plans and interior condition sets occur in rule payloads.
The producer's success is observed by execution; every successful value has
a checked typed boundary and support, without an unproved compiler axiom. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.GeneratedSharedMAC
open Foundation.Logic.SharedInference
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false

abbrev Output (stage : Nat) := CellPresentation.Verified MACNormalization.layout MACNormalization.relators
  ⟨.stage stage, .finish, MACNormalization.direct stage, MACNormalization.strategy.normal (.stage stage),
    (MACNormalization.generated stage).needs MACNormalization.layout MACNormalization.relators⟩

def compileMode (sharing : Bool) (stage : Nat) : Option (Output stage) :=
  CellPresentation.compileMode sharing (MACNormalization.generated stage)

def compile (stage : Nat) : Option (Output stage) := compileMode true stage

def stats (stage : Nat) : Option (Nat × Nat × Nat × Nat × Nat × Nat) := do
  let output ← compile stage
  pure ((CellPresentation.toTree (MACNormalization.generated stage)).nodeCount,
    output.data.nodeCount, output.data.referenceCount,
    (output.data.encode CellPresentation.render).utf8ByteSize,
    ((MACNormalization.generated stage).needs MACNormalization.layout MACNormalization.relators).card,
    ((MACNormalization.generated stage).fresh MACNormalization.layout MACNormalization.relators {1}).card)

theorem comparison (orders : Nat → Schedule 8) (stage : Nat) (output : Output stage) :
    ∃ left : Holds (MACNormalization.condition orders) ((MACNormalization.direct stage).needs MACNormalization.layout),
    ∃ right : Holds (MACNormalization.condition orders)
        ((MACNormalization.strategy.normal (.stage stage)).needs MACNormalization.layout),
    Comparison (evaluate (MACNormalization.baseModel orders) (MACNormalization.direct stage) left)
      (evaluate (MACNormalization.baseModel orders) (MACNormalization.strategy.normal (.stage stage)) right) :=
  output.probabilistic (MACNormalization.model orders) (MACNormalization.conditions orders _)

theorem ordinary_comparison (orders : Nat → Schedule 8) (stage : Nat) (output : Output stage) :
    Comparison
      (evaluate (MACNormalization.baseModel orders) (MACNormalization.direct stage) (MACNormalization.conditions orders _))
      (evaluate (MACNormalization.baseModel orders) (MACNormalization.strategy.normal (.stage stage)) (MACNormalization.conditions orders _)) :=
  (sound (CellPresentation.ordinary (MACNormalization.model orders)
    (fun label => GameCoherence.Examples.MAC.full_security (orders label))) output.data output.accepted).some

theorem repaired (old updated : Nat → Schedule 8) (stage : Nat) (output : Output stage) (changed : Finset Nat)
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (MACNormalization.condition updated)
      ((MACNormalization.generated stage).fresh MACNormalization.layout MACNormalization.relators changed)) :
    ∃ left : Holds (MACNormalization.condition updated) ((MACNormalization.direct stage).needs MACNormalization.layout),
    ∃ right : Holds (MACNormalization.condition updated)
        ((MACNormalization.strategy.normal (.stage stage)).needs MACNormalization.layout),
    Comparison (evaluate (MACNormalization.baseModel updated) (MACNormalization.direct stage) left)
      (evaluate (MACNormalization.baseModel updated) (MACNormalization.strategy.normal (.stage stage)) right) := by
  apply output.repaired (MACNormalization.model updated) changed (MACNormalization.conditions old _) _ rechecked
  intro label outside cached
  simpa only [MACNormalization.condition, ← unchanged label outside] using cached

def rejectsMissingInterior : Bool :=
  match compile 3 with
  | none => false
  | some output => decide (check output.data ≠ some
      ⟨.stage 3, .finish, MACNormalization.direct 3, MACNormalization.strategy.normal (.stage 3),
        ((MACNormalization.generated 3).needs MACNormalization.layout MACNormalization.relators).erase 1⟩)

/-- info: (true, true) -/
#guard_msgs in
#eval (rejectsMissingInterior,
  ((PlanShape.seq (.identity MACNormalization.Vertex.finish) (.atom (MACNormalization.Atom.schedule 0))).decode
    MACNormalization.layout).isNone)

/-- info: [(0, some (48, 24, 29, 25709, 1, 0)), (1, some (89, 55, 69, 74531, 2, 1)), (2, some (130, 88, 109, 135058, 3, 1)), (3, some (171, 121, 149, 206891, 4, 1)), (4, some (212, 154, 189, 290255, 5, 1))] -/
#guard_msgs (whitespace := lax) in
#eval [0, 1, 2, 3, 4].map (fun stage => (stage, stats stage))

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.GeneratedSharedMAC
