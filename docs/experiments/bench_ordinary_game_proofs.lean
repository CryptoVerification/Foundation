import Foundation.Examples.GameProofOrdinaryMAC

/-! Independent ordinary generation versus the previous general diagram
generator, with the ordinary construction also lifted geometrically as a
control. All use one finite-support goal, rule library, producer and checker.
This is a comparison of these algorithms on one MAC family, not a dimension
separation or a measurement of semantic proof/kernel checking. -/
open Foundation.Logic.SharedInference
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples

abbrev InputTree := Foundation.Logic.SharedInference.Tree (CellPresentation.Rule MACNormalization.layout Nat)

inductive Method where | general | ordinary | specialized deriving Repr

def methodName : Method → String
  | .general => "general_diagram"
  | .ordinary => "ordinary"
  | .specialized => "specialized_diagram"

@[noinline] def inputTree (method : Method) (stage : Nat) : InputTree :=
  match method with
  | .general => CellPresentation.toTree (MACNormalization.generated stage)
  | .ordinary => OrdinaryMAC.tree stage
  | .specialized => CellPresentation.toTree (OrdinaryMAC.specializedGeometric stage).1

def payload (tree : InputTree) : Nat :=
  match tree with
  | .node rule children => (CellPresentation.render rule).utf8ByteSize + (children.map payload).sum

def measureRow (sample stage : Nat) (method : Method) (goalBytes : Nat) : IO Unit := do
  let started ← IO.monoNanosNow
  let tree := inputTree method stage
  let sourceNodes := tree.nodeCount
  let sourcePayload := payload tree
  if sourceNodes == 0 || sourcePayload == 0 then throw (IO.userError "Empty source")
  let generated ← IO.monoNanosNow
  let some output := CellPresentation.FiniteOrdinary.compileAt
      (relators := MACNormalization.relators) (OrdinaryMAC.claim stage) tree
    | throw (IO.userError s!"Rejected output at stage {stage}: {methodName method}")
  if output.data.nodeCount == 0 then throw (IO.userError "Empty certificate")
  let compiled ← IO.monoNanosNow
  let size := (output.data.encode CellPresentation.render).utf8ByteSize
  if size == 0 then throw (IO.userError "Empty encoding")
  let encoded ← IO.monoNanosNow
  if output.data.expandedSize != some sourceNodes then throw (IO.userError "Expansion count changed")
  let needed := (OrdinaryMAC.support stage).card
  let freshCount := (fresh (OrdinaryMAC.support stage) {1}).card
  IO.println s!"{sample},{stage},{methodName method},{sourceNodes},{sourcePayload},{output.data.nodeCount},{output.data.referenceCount},{size},{goalBytes},{needed},{freshCount},{generated - started},{compiled - generated},{encoded - compiled}"

def main : IO Unit := do
  IO.println "sample,mac_stage,method,source_tree_nodes,source_payload_bytes,certificate_rows,references,encoded_bytes,goal_display_bytes,conditions,fresh_conditions,generation_accounting_ns,interning_validation_ns,encoding_ns"
  for sample in [0:3] do
    let methods := match sample % 3 with
      | 0 => [Method.general, .ordinary, .specialized]
      | 1 => [Method.ordinary, .specialized, .general]
      | _ => [Method.specialized, .general, .ordinary]
    for stage in [0, 1, 2, 3, 4] do
      let goal := OrdinaryMAC.claim stage
      let goalBytes := (reprStr (goal.source, goal.target, goal.left.shape, goal.right.shape, goal.support.sort (· ≤ ·))).utf8ByteSize
      if goalBytes == 0 then throw (IO.userError "Empty goal")
      for method in methods do
        measureRow sample stage method goalBytes
