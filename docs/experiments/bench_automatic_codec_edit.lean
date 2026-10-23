import Foundation.Examples.RandomFunctionMACAutomaticEdit

/-! Acceptance-only comparison with automatic exact difference extraction,
and with construction of the concrete replacement word. Shared-lemma and
diagram paths get the same declarations, old certificate and exact scope.
Initial certification, proving scope coverage, kernel checking, game execution
and applying inverse functions are outside these timers. -/
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

@[noinline] private def automatic (salt : Nat) : Bool :=
  (FiniteCodecDifference.compile finiteScope ignoredDeclaration (varied salt) scoped_accepts).isSome

@[noinline] private def withPath (salt : Nat) : Bool :=
  automatic salt &&
    ((CryptoOracle.RandomOracle.Representation.Patches.generated
      RandomFunctionMACAutomaticEdit.rows ignoredDeclaration (varied salt)).length == 2)

private def measureBatch (method : Nat → Bool) (sample offset runs : Nat) (name : String) : IO Unit := do
  let start ← IO.monoNanosNow
  let mut accepted := 0
  for i in [0:runs] do
    if method (offset + i) then accepted := accepted + 1
  let elapsed := (← IO.monoNanosNow) - start
  if accepted != runs then throw (IO.userError s!"Rejected a bijective declaration: {name}, {accepted}/{runs}")
  IO.println s!"{sample},{name},{runs},{elapsed},{accepted}"

def main : IO Unit := do
  if !(full 123 && incremental 124 && automatic 125 && withPath 126) then
    throw (IO.userError "Warmup failed")
  IO.println "sample,method,runs,nanoseconds,accepted"
  let methods : Array (String × (Nat → Bool)) :=
    #[("full", full), ("incremental", incremental), ("automatic", automatic), ("automatic_with_path", withPath)]
  for sample in [0:7] do
    for position in [0:4] do
      let method := methods[(sample + position) % 4]!
      measureBatch method.2 sample (sample * 32) 16 method.1
