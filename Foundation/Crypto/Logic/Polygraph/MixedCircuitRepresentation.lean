import Foundation.Crypto.Logic.Polygraph.MixedCircuit

/-! Box-wise deterministic changes of port representation extend to the
original mixed syntax, including noninjective maps, copy and discard. These
are semantic representation maps, not unit-cost machine instructions. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open Foundation.Probability
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Box Requirement Budget : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {condition : Requirement → Prop}
variable {Old New : signature.PortAtom → Type}
set_option backward.isDefEq.respectTransparency false

structure Representation (old : Model signature condition Old) (updated : Model signature condition New)
    (maps : ∀ atom, Old atom → New atom) : Prop where
  box : ∀ label (valid : Holds condition (signature.needs label)) input,
    (old.box label valid input).map ((signature.outputs label).map maps) =
      updated.box label valid ((signature.inputs label).map maps input)

theorem Representation.evaluate {old : Model signature condition Old} {updated : Model signature condition New}
    {maps : ∀ atom, Old atom → New atom} (representation : Representation old updated maps)
    {n m} (circuit : Circuit signature n m) (valid : Holds condition circuit.needs) (input : Bundle Old n) :
    (MixedCircuit.evaluate old circuit valid input).map (m.map maps) =
      MixedCircuit.evaluate updated circuit valid (n.map maps input) := by
  induction circuit with
  | wire wire => simpa only [MixedCircuit.evaluate, PMF.pure_map] using congrArg PMF.pure (wire.naturality maps input)
  | box label => exact representation.box label valid input
  | seq first second one two =>
      simp only [MixedCircuit.evaluate, PMF.map_bind]
      simp_rw [two]
      rw [← one (valid.restrict Finset.subset_union_left) input, PMF.bind_map]
      rfl
  | @tensor n m n' m' first second one two =>
      simp only [MixedCircuit.evaluate, PMF.map_bind, PMF.map_comp, append, Shape.map, Function.comp_def]
      have right (left : Bundle Old m) := congrArg
        (PMF.map (fun output : Bundle New m' => (m.map maps left, output)))
        (two (valid.restrict Finset.subset_union_right) input.2)
      simp only [PMF.map_comp, Function.comp_def] at right
      simp_rw [right]
      rw [← one (valid.restrict Finset.subset_union_left) input.1, PMF.bind_map]
      rfl

end CryptoLogic.Polygraph.MixedCircuit
