import Foundation.Examples.RandomFunctionMACIncrementalEdit

/-! Acceptance-only timing experiment. Both methods receive the same finite
scope and encoding declaration. The incremental method additionally reuses an
old acceptance certificate and unchanged-row proof. Scope extraction, initial
certification, proof construction, game execution and function application are
outside the timer. This ordinary shared-lemma implementation contains no
polygraphic algorithm and cannot establish a higher-dimensional advantage. -/
open Foundation.Logic Foundation.Symmetric
open RandomFunctionMACScopedEdit
open RandomFunctionMACGeneratedEdit (ignoredDeclaration)

private def varied (salt : Nat) (index : Bool × Fin 8) (tag : Fin 256) : Fin 256 :=
  if index.2 = 7 then tag + Fin.ofNat 256 (salt + if index.1 then 3 else 2)
  else ignoredDeclaration index tag

private theorem unchanged (salt : Nat) : ∀ index ∈ finiteScope,
    index ∉ changed → ignoredDeclaration index = varied salt index := by
  intro index _ untouched
  have different : index.2 ≠ 7 := by
    intro same
    exact untouched (Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr same⟩)
  funext tag
  simp only [varied, if_neg different]

@[noinline] private def full (salt : Nat) : Bool :=
  (FiniteCodecRestriction.compile finiteScope (varied salt)).isSome

@[noinline] private def incremental (salt : Nat) : Bool :=
  (FiniteCodecRepair.compile finiteScope changed ignoredDeclaration (varied salt)
    scoped_accepts (unchanged salt)).isSome

private def measureBatch (method : Nat → Bool) (sample offset runs : Nat) (name : String) : IO Unit := do
  let start ← IO.monoNanosNow
  let mut accepted := 0
  for i in [0:runs] do
    if method (offset + i) then accepted := accepted + 1
  let elapsed := (← IO.monoNanosNow) - start
  if accepted != runs then throw (IO.userError s!"Rejected a bijective declaration: {name}, {accepted}/{runs}")
  IO.println s!"{sample},{name},{runs},{elapsed},{accepted}"

def main : IO Unit := do
  -- Warm both methods; discard their times. Variable salts prevent measuring
  -- a single constant result, and noinline prevents call-site specialization.
  let a := full 123
  let b := incremental 124
  if !(a && b) then throw (IO.userError "Warmup failed")
  IO.println "sample,method,runs,nanoseconds,accepted"
  for sample in [0:7] do
    if sample % 2 == 0 then
      measureBatch full sample (sample * 32) 16 "full"
      measureBatch incremental sample (sample * 32) 16 "incremental"
    else
      measureBatch incremental sample (sample * 32) 16 "incremental"
      measureBatch full sample (sample * 32) 16 "full"
