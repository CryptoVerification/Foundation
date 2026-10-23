import Foundation.Crypto.Logic.Polygraph.MixedCircuitHigherNormalization
import Foundation.Examples.MixedCircuitMACGuardedNormalization

/-! Actual higher witnesses for the MAC rewrite catalogue, and a comparison
of contextual lifting with this repository's global normalization algorithm.
Any extra guard observed below is algorithmic, not semantically necessary.
No exclusive higher-dimensional advantage or new crypto bound is claimed. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false

def orderLeft (stage : Nat) : Path (relators := relators)
    (.tensor (before stage) (before (stage + 1))) (.tensor (after stage) (after (stage + 1))) :=
  .cons (.tensorLeft (rewrite stage) (before (stage + 1)))
    (RewritePath.single (.tensorRight (after stage) (rewrite (stage + 1))))

def orderRight (stage : Nat) : Path (relators := relators)
    (.tensor (before stage) (before (stage + 1))) (.tensor (after stage) (after (stage + 1))) :=
  .cons (.tensorRight (before stage) (rewrite (stage + 1)))
    (RewritePath.single (.tensorLeft (rewrite stage) (after (stage + 1))))

def localDiagram (stage : Nat) : Homotopy (Track.ofPath (orderLeft stage)) (Track.ofPath (orderRight stage)) :=
  .generator (.separated (.tensorLR (rewrite stage) (rewrite (stage + 1))))

def generatedDiagram (stage : Nat) : Homotopy (Track.ofPath (orderLeft stage)) (Track.ofPath (orderRight stage)) :=
  directedCoherence normalizationStrategy roots_rigid (orderLeft stage) (orderRight stage)

def framedLeft (stage : Nat) : Path (relators := relators)
    (.tensor (.tensor (before stage) (before (stage + 1))) (before (stage + 2)))
    (.tensor (.tensor (after stage) (after (stage + 1))) (before (stage + 2))) :=
  .cons (.tensorLeft (.tensorLeft (rewrite stage) (before (stage + 1))) (before (stage + 2)))
    (RewritePath.single (.tensorLeft (.tensorRight (after stage) (rewrite (stage + 1))) (before (stage + 2))))

def framedRight (stage : Nat) : Path (relators := relators)
    (.tensor (.tensor (before stage) (before (stage + 1))) (before (stage + 2)))
    (.tensor (.tensor (after stage) (after (stage + 1))) (before (stage + 2))) :=
  .cons (.tensorLeft (.tensorRight (before stage) (rewrite (stage + 1))) (before (stage + 2)))
    (RewritePath.single (.tensorLeft (.tensorLeft (rewrite stage) (after (stage + 1))) (before (stage + 2))))

/-- The untouched third component is a frame. Only the local diagram is
lifted; the frame is not normalized by this constructor. -/
def localFramed (stage : Nat) : Homotopy (Track.ofPath (framedLeft stage)) (Track.ofPath (framedRight stage)) :=
  Homotopy.whisker (.tensorLeft (before (stage + 2))) (localDiagram stage)

def generatedFramed (stage : Nat) : Homotopy (Track.ofPath (framedLeft stage)) (Track.ofPath (framedRight stage)) :=
  directedCoherence normalizationStrategy roots_rigid (framedLeft stage) (framedRight stage)

theorem local_support (stage : Nat) : Homotopy.support (localDiagram stage) = {stage, stage + 1, stage + 2} := by
  ext label
  simp [localDiagram, Homotopy.support, Exchange.support, Step.support, rewrite, Primitive.support, Relator.support,
    relators, before, after, Circuit.needs, signature, MACNormalization.layout]

theorem local_framed_support (stage : Nat) : Homotopy.support (localFramed stage) = {stage, stage + 1, stage + 2} := by
  rw [localFramed, Homotopy.whisker_support, local_support]
  ext label
  simp [Placement.needs, before, Circuit.needs, signature, MACNormalization.layout]

theorem local_framed_constructorCount (stage : Nat) : Homotopy.constructorCount (localFramed stage) = 1 := by
  rw [localFramed, Homotopy.whisker_constructorCount]
  rfl

theorem local_avoids_frame_successor (stage : Nat) :
    fresh (Homotopy.support (localFramed stage)) {stage + 3} = ∅ := by
  rw [local_framed_support]
  ext label
  simp only [fresh, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
  omega

/-- The canonical algorithm introduces an interior guard that the local
construction avoids. This is a finite concrete fact, not an all-stage bound. -/
theorem generated_uses_extra_guard : 3 ∈ Homotopy.support (generatedFramed 0) := by
  apply directedCoherence_suffix_support normalizationStrategy roots_rigid (framedLeft 0) (framedRight 0)
  decide_cbv

theorem original_routes_avoid_extra_guard : 3 ∉ Path.support (framedLeft 0) ∪ Path.support (framedRight 0) := by decide_cbv

/-- Reuse the actual checked updated MAC kernels, retaining every interior
guard of the higher witness rather than just the two outer tracks. -/
theorem local_repaired (old updated : Nat → Schedule 8) (stage : Nat) (changed : Finset Nat)
    (cached : Holds (MACNormalization.condition old) (Homotopy.support (localFramed stage)))
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (MACNormalization.condition updated) (fresh (Homotopy.support (localFramed stage)) changed)) :
    Holds (MACNormalization.condition updated) (RewriteTrack.support (Track.ofPath (framedLeft stage))) ∧
    Holds (MACNormalization.condition updated) (RewriteTrack.support (Track.ofPath (framedRight stage))) ∧
    ∃ left : Holds (MACNormalization.condition updated) (Circuit.tensor (.tensor (before stage) (before (stage + 1))) (before (stage + 2))).needs,
    ∃ right : Holds (MACNormalization.condition updated) (Circuit.tensor (.tensor (after stage) (after (stage + 1))) (before (stage + 2))).needs,
      ∀ input, evaluate (base updated) _ left input = evaluate (base updated) _ right input := by
  apply Homotopy.repaired (model updated) (localFramed stage) changed cached _ rechecked
  intro label outside valid
  simpa only [MACNormalization.condition, ← unchanged label outside] using valid

/-- info: [(0, 1, 3, 0, 1, 4, 1), (1, 1, 3, 0, 1, 4, 1), (2, 1, 3, 0, 1, 4, 1)] -/
#guard_msgs in
#eval [0, 1, 2].map (fun stage =>
  let focused := localFramed stage
  let canonical := generatedFramed stage
  (stage, Homotopy.exchangeCount focused, (Homotopy.support focused).card,
    (fresh (Homotopy.support focused) {stage + 3}).card,
    Homotopy.exchangeCount canonical, (Homotopy.support canonical).card,
    (fresh (Homotopy.support canonical) {stage + 3}).card))

/-- info: [(0, 1, 255), (1, 1, 255), (2, 1, 255)] -/
#guard_msgs in
#eval [0, 1, 2].map (fun stage => (stage,
  Homotopy.constructorCount (localFramed stage), Homotopy.constructorCount (generatedFramed stage)))

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC
