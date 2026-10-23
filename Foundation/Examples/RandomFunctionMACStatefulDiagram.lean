import Foundation.Crypto.Semantics.Oracle.StatefulDiagramExchange
import Foundation.Examples.RandomFunctionMACQueryFootprint

/-! Read/write-typed finite diagram for the ORIGINAL coin and four-query MAC
caller. All queries share one cache and one ordered transcript. Dependencies
are computed from these interfaces, not inferred from opaque host functions. -/
namespace Foundation.Symmetric.RandomFunctionMACStatefulDiagram
set_option backward.isDefEq.respectTransparency false
open Foundation.Probability CryptoOracle CryptoOracle.RandomOracle CryptoOracle.StatefulDiagram
open RandomFunctionMACNativeCaller (target firstMessage secondMessage)

inductive Slot where
  | coin | first | second | repeated | cache | trace | result
  deriving DecidableEq, Repr
inductive Op where
  | coin | first | second | repeated | verify
  deriving DecidableEq, Repr

structure Data where
  bit : Bool := false
  tag : Fin 256 := 0
  saved : Table (Fin 8) (Fin 256) := []
  log : List (Fin 8 × Fin 256) := []

def signature : Op → Interface Slot
  | .coin => ⟨∅, {.coin}⟩
  | .first => ⟨{.coin, .cache, .trace}, {.first, .cache, .trace}⟩
  | .second => ⟨{.first, .cache, .trace}, {.second, .cache, .trace}⟩
  | .repeated => ⟨{.coin, .cache, .trace}, {.repeated, .cache, .trace}⟩
  | .verify => ⟨{.coin, .second, .repeated, .cache, .trace}, {.result, .cache, .trace}⟩

def diagram : List Op := [.coin, .first, .second, .repeated, .verify]

def initial (saved : Table (Fin 8) (Fin 256)) : Store Slot Data :=
  fun slot => if slot = .cache then {saved := saved} else {}

def observe (store : Store Slot Data) : Outcome (Fin 8) (Fin 256) Bool (Table (Fin 8) (Fin 256)) :=
  ⟨(store .result).bit, (store .cache).saved, (store .trace).log⟩

private def inputs {op : Op} (values : (signature op).reads → Data)
    (slot : Slot) (member : slot ∈ (signature op).reads) : Data := values ⟨slot, member⟩

private def queryOutputs (tagSlot : Slot) (log : List (Fin 8 × Fin 256)) (request : Fin 8)
    (answer : Table (Fin 8) (Fin 256) × Fin 256) (slot : Slot) : Data :=
  if slot = .cache then {saved := answer.1} else
  if slot = .trace then {log := log ++ [(request, answer.2)]} else
  if slot = tagSlot then {tag := answer.2} else {}

noncomputable def kernels (world : Oracle (Fin 8) (Fin 256) (Table (Fin 8) (Fin 256))) : Kernels signature Data
  | .coin, _ => sampleBit.map fun bit => fun _ => {bit := bit}
  | .first, values =>
      let request := firstMessage (inputs values .coin (by decide)).bit
      (world (inputs values .cache (by decide)).saved request).map fun answer =>
        fun slot => queryOutputs .first (inputs values .trace (by decide)).log request answer slot
  | .second, values =>
      let request := secondMessage (inputs values .first (by decide)).tag
      (world (inputs values .cache (by decide)).saved request).map fun answer =>
        fun slot => queryOutputs .second (inputs values .trace (by decide)).log request answer slot
  | .repeated, values =>
      let request := firstMessage (inputs values .coin (by decide)).bit
      (world (inputs values .cache (by decide)).saved request).map fun answer =>
        fun slot => queryOutputs .repeated (inputs values .trace (by decide)).log request answer slot
  | .verify, values =>
      let candidate := if (inputs values .coin (by decide)).bit then
        (inputs values .repeated (by decide)).tag else (inputs values .second (by decide)).tag
      (world (inputs values .cache (by decide)).saved 7).map fun answer => fun slot =>
        if (slot : Slot) = .result then {bit := decide (answer.2 = candidate)}
        else queryOutputs .result (inputs values .trace (by decide)).log 7 answer slot

/-- Full operational refinement, for ANY shared oracle and initial cache. -/
theorem actual_caller (world : Oracle (Fin 8) (Fin 256) (Table (Fin 8) (Fin 256)))
    (saved : Table (Fin 8) (Fin 256)) :
    (execute signature (kernels world) diagram (initial saved)).map observe = target.run world saved := by
  simp [execute, StatefulDiagram.step, kernels, diagram, signature, inputs, view, write, initial, observe,
    queryOutputs, target, Program.run, PMF.map_bind, PMF.bind_map, PMF.pure_map,
    PMF.map_comp, Function.comp_def, List.append_assoc]
  rfl

/-- Observing the complete retained outcome requires all five boxes. -/
theorem full_required : required signature diagram {.result, .cache, .trace} =
    ({.coin, .first, .second, .repeated, .verify} : Finset Op) := by
  ext op
  cases op <;> simp [required, dependencies, neededBefore, signature, diagram, Finset.disjoint_left]

theorem verification_only_obligation : obligations signature diagram {.result, .cache, .trace} {.verify} =
    ({.verify} : Finset Op) := by
  rw [obligations, full_required]
  decide

/-- info: (5, 1, false) -/
#guard_msgs in
#eval ((required signature diagram {.result, .cache, .trace}).card,
  (obligations signature diagram {.result, .cache, .trace} {.verify}).card,
  checkReuse signature diagram {.result, .cache, .trace} {.verify})

/-- A genuine probabilistic rewrite: relabel the fresh uniform response before
caching and returning it. Cache hits still return the saved response. -/
noncomputable def freshPermutation (permutation : Fin 256 ≃ Fin 256) :
    Oracle (Fin 8) (Fin 256) (Table (Fin 8) (Fin 256)) := fun saved input =>
  match saved.lookup input with
  | some tag => PMF.pure (saved, tag)
  | none => (uniform (Fin 256)).map fun tag => ((input, permutation tag) :: saved, permutation tag)

theorem freshPermutation_eq (permutation : Fin 256 ≃ Fin 256) : freshPermutation permutation = RandomOracle.oracle := by
  funext saved input
  cases found : saved.lookup input with
  | some tag => simp only [freshPermutation, RandomOracle.oracle, found]
  | none =>
      simp only [freshPermutation, RandomOracle.oracle, found]
      have uniformLaw := uniform_map_equiv permutation
      have mapped := congrArg (fun p => p.map (fun tag => ((input, tag) :: saved, tag))) uniformLaw
      simpa only [PMF.map_comp, Function.comp_def] using mapped

noncomputable def editedKernels (permutation : Fin 256 ≃ Fin 256) : Kernels signature Data :=
  fun op => if op = .verify then kernels (freshPermutation permutation) op else kernels RandomOracle.oracle op

theorem unchanged_operations (permutation : Fin 256 ≃ Fin 256) (op : Op) (untouched : op ∉ ({.verify} : Finset Op)) :
    kernels RandomOracle.oracle op = editedKernels permutation op := by
  have different : op ≠ .verify := by simpa only [Finset.mem_singleton] using untouched
  simp only [editedKernels, if_neg different]

/-- Discharge precisely the generated one-box obligation. -/
theorem generated_local_laws (permutation : Fin 256 ≃ Fin 256) :
    ∀ op ∈ obligations signature diagram {.result, .cache, .trace} {.verify},
      kernels RandomOracle.oracle op = editedKernels permutation op := by
  rw [verification_only_obligation]
  intro op member
  have same : op = .verify := Finset.mem_singleton.mp member
  subst op
  simp only [editedKernels, if_true, freshPermutation_eq]

attribute [local irreducible] signature diagram kernels editedKernels

private def decodeView (values : ({.result, .cache, .trace} : Finset Slot) → Data) :
    Outcome (Fin 8) (Fin 256) Bool (Table (Fin 8) (Fin 256)) :=
  ⟨(values ⟨.result, by decide⟩).bit, (values ⟨.cache, by decide⟩).saved, (values ⟨.trace, by decide⟩).log⟩

/-- Use the computed obligations to certify the edited probabilistic box in
its real shared-state MAC context, retaining cache and complete transcript. -/
theorem repaired_actual_game (permutation : Fin 256 ≃ Fin 256) (saved : Table (Fin 8) (Fin 256)) :
    (execute signature (editedKernels permutation) diagram (initial saved)).map observe =
      target.run RandomOracle.oracle saved := by
  have unchanged := unchanged_operations permutation
  have repaired := generated_local_laws permutation
  generalize old_eq : kernels RandomOracle.oracle = oldWorld at unchanged repaired
  generalize new_eq : editedKernels permutation = newWorld at unchanged repaired ⊢
  have law :
      (execute signature oldWorld diagram (initial saved)).map (view ({.result, .cache, .trace} : Finset Slot)) =
      (execute signature newWorld diagram (initial saved)).map (view ({.result, .cache, .trace} : Finset Slot)) := by
    apply repair_sound (signature := signature) (left := oldWorld) (right := newWorld)
      (diagram := diagram) (needed := {.result, .cache, .trace}) (changed := {.verify}) (store := initial saved)
    · exact unchanged
    · exact repaired
  have projected := congrArg (fun (p : PMF (({.result, .cache, .trace} : Finset Slot) → Data)) => p.map decodeView) law
  simp only [PMF.map_comp, Function.comp_def] at projected
  change (execute signature oldWorld diagram (initial saved)).map observe =
    (execute signature newWorld diagram (initial saved)).map observe at projected
  rw [← old_eq, actual_caller] at projected
  exact projected.symm

/-- The shared cache prevents an automatic exchange of two real queries. -/
theorem shared_queries_rejected : checkExchange signature .first .second = false := by
  simp [checkExchange, Independent, signature, Finset.disjoint_left]

/-- Diagnostic: two boxes read the same immutable coin but write separate
registers. This is not a replacement for the actual MAC caller. -/
def forkSignature (which : Bool) : Interface Slot :=
  ⟨{.coin}, if which then {.first} else {.second}⟩

def independentCertificate : Exchange forkSignature [false, true] [true, false] :=
  .swap [] [] false true (by decide)

theorem independent_full_state (world : Kernels forkSignature Data) (store : Store Slot Data) :
    execute forkSignature world [false, true] store = execute forkSignature world [true, false] store :=
  independentCertificate.sound forkSignature world store

/-- info: (false, true) -/
#guard_msgs in
#eval ((attemptExchange signature [] [] .first .second).isSome,
  (attemptExchange forkSignature [] [] false true).isSome)

end Foundation.Symmetric.RandomFunctionMACStatefulDiagram
