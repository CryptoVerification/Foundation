import Foundation.Examples.GameProofGeneratedSharedMAC

/-! Actual MAC normalizer-output experiment. Both modes start from the same
generated Cell and use the same typed/support checker. Ordinary semantic
proofs may use the identical shared certificate; this is not a claim of a
geometric/ordinary speed difference. Timers force their results. -/
open Foundation.Logic.SharedInference
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples

private def payload (tree : Foundation.Logic.SharedInference.Tree (CellPresentation.Rule MACNormalization.layout Nat)) : Nat :=
  match tree with
  | .node rule children => (CellPresentation.render rule).utf8ByteSize + (children.map payload).sum

@[noinline] private def make (stage : Nat) := MACNormalization.generated stage

private def measureRow (sample stage : Nat) : IO Unit := do
  let began ← IO.monoNanosNow
  let source := make stage
  let tree := CellPresentation.toTree source
  let sourceNodes := tree.nodeCount
  let sourcePayload := payload tree
  if sourceNodes == 0 || sourcePayload == 0 then throw (IO.userError "Empty source")
  let generated ← IO.monoNanosNow
  let modes := if sample % 2 == 0 then [true, false] else [false, true]
  for sharing in modes do
    let started ← IO.monoNanosNow
    let some output := CellPresentation.compileMode sharing source
      | throw (IO.userError s!"Compilation rejected at stage {stage}")
    if output.data.nodeCount == 0 then throw (IO.userError "Empty output")
    let compiled ← IO.monoNanosNow
    let size := (output.data.encode CellPresentation.render).utf8ByteSize
    if size == 0 then throw (IO.userError "Empty encoding")
    let encoded ← IO.monoNanosNow
    if output.data.expandedSize != some sourceNodes then throw (IO.userError "Expansion count changed")
    if !sharing && output.data.nodeCount != sourceNodes then throw (IO.userError "Unshared count changed")
    IO.println s!"{sample},{stage},{sharing},{sourceNodes},{sourcePayload},{output.data.nodeCount},{output.data.referenceCount},{size},{generated - began},{compiled - started},{encoded - compiled}"

def main : IO Unit := do
  IO.println "sample,mac_stage,sharing,source_tree_nodes,source_payload_bytes,certificate_rows,references,encoded_bytes,generation_accounting_ns,lowering_validation_ns,encoding_ns"
  for sample in [0:3] do
    for stage in [0, 1, 2, 3, 4] do
      measureRow sample stage
