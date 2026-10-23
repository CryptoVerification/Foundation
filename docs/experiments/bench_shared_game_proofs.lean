import Foundation.Examples.GameProofSharedMAC

/-! Relative certificate-data experiment, not Lean-kernel proof timing.
Both geometric and ordinary semantic interpretations consume the same
certificate, local lemma library, and checker. Only this checker is timed.
The source family deliberately repeats one MAC comparison, so the expanded
tree is not a minimal proof. A one-node proof is available to both models.
Run: nix develop path:. -c lake env lean --run docs/experiments/bench_shared_game_proofs.lean
-/
open Foundation.Logic.SharedInference
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.SharedMAC

@[noinline] private def build (n : Nat) : Certificate theory := certificate n
@[noinline] private def verify (input : Certificate theory) : Bool := check input == some (false, false)
@[noinline] private def bytes (input : Certificate theory) : Nat := (input.encode render).utf8ByteSize

private def row (sample n : Nat) : IO Unit := do
  let started ← IO.monoNanosNow
  let input := build n
  -- Force the complete finite payload before stopping the first timer.
  -- This phase includes accounting scans; it is not a pure allocation timer.
  if input.nodeCount != n + 3 || input.referenceCount != 2 * n + 3 ||
      input.lookupSteps != n * n + 5 * n + 4 || input.payloadCost (fun rule => (render rule).utf8ByteSize) != 18 * n + 29 then
    throw (IO.userError s!"Incorrect accounting at level {n}")
  let constructed ← IO.monoNanosNow
  let ok := verify input
  if !ok then throw (IO.userError s!"Rejected certificate at level {n}")
  let checked ← IO.monoNanosNow
  let size := bytes input
  if size < input.nodeCount then throw (IO.userError "Incomplete encoding")
  let encoded ← IO.monoNanosNow
  let expanded := input.expandedSize
  IO.println s!"{sample},{n},{input.nodeCount},{input.referenceCount},{input.lookupSteps},{expanded.getD 0},{size},{constructed - started},{checked - constructed},{encoded - checked}"

def main : IO Unit := do
  IO.println "sample,level,nodes,references,linked_lookup_steps,expanded_tree_nodes,encoded_bytes,construction_accounting_ns,check_ns,encoding_ns"
  for sample in [0:3] do
    for n in [0, 4, 16, 64, 256, 1024] do
      row sample n
  let simple := bytes reflexive
  IO.println s!"reflexive_control,1,0,{simple}"
