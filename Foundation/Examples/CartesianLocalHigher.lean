import Foundation.Crypto.Logic.Polygraph.MixedCartesianLocalHigher
import Foundation.Examples.TypedCartesianWiring

/-! Actual duplicated/erased-argument diagrams with bounded rewrite boundaries,
plus the existing full-state MAC kernel in a surrounding context. These are
local examples, not a proof of global cartesian higher coherence. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.Examples
variable {Atom : Type}

def copyStep (shape : Shape Atom) : Step (.copy shape) (fork (.identity shape) (.identity shape)) := .root (.copyExpand shape)
def etaCell (shape : Shape Atom) := argumentCell (Variation.eta shape shape shape) (copyStep shape)
def eraseCell (shape : Shape Atom) := argumentCell (Variation.betaFstLast (Wire.identity shape)) (copyStep shape)
def duplicateCell (shape : Shape Atom) := argumentCell (Variation.forkFirst (fst shape shape) (snd shape shape)) (copyStep shape)

theorem eta_counts (shape : Shape Atom) :
    (stepCount (beforeRule (Variation.eta shape shape shape) (copyStep shape)),
      stepCount (afterRule (Variation.eta shape shape shape) (copyStep shape))) = (3, 2) := by rfl

theorem erase_counts (shape : Shape Atom) :
    (stepCount (beforeRule (Variation.betaFstLast (Wire.identity shape)) (copyStep shape)),
      stepCount (afterRule (Variation.betaFstLast (Wire.identity shape)) (copyStep shape))) = (2, 1) := by rfl

theorem duplicate_counts (shape : Shape Atom) :
    (stepCount (beforeRule (Variation.forkFirst (fst shape shape) (snd shape shape)) (copyStep shape)),
      stepCount (afterRule (Variation.forkFirst (fst shape shape) (snd shape shape)) (copyStep shape))) = (2, 3) := by rfl

def a : Shape (Fin 2) := .atom 0
def b : Shape (Fin 2) := .atom 1

/-- info: ((3, 2), (2, 1), (2, 3), 1) -/
#guard_msgs in
#eval ((stepCount (beforeRule (.eta a a a) (copyStep a)), stepCount (afterRule (.eta a a a) (copyStep a))),
  (stepCount (beforeRule (.betaFstLast (.identity a)) (copyStep a)), stepCount (afterRule (.betaFstLast (.identity a)) (copyStep a))),
  (stepCount (beforeRule (.forkFirst (fst a a) (snd a a)) (copyStep a)), stepCount (afterRule (.forkFirst (fst a a) (snd a a)) (copyStep a))),
  Homotopy.constructorCount (etaCell a))

/-- info: (9, 6, 11, 12, 13) -/
#guard_msgs in
#eval ((argumentAt (.eta (.copy a)) (0 : Fin 1)).variation.code.val,
  (argumentAt (.betaFst (.identity a) (.copy a)) (1 : Fin 2)).variation.code.val,
  (argumentAt (.forkAfter (.copy a) (fst a a) (snd a a)) (0 : Fin 3)).variation.code.val,
  (argumentAt (.forkAfter (.copy a) (fst a a) (snd a a)) (1 : Fin 3)).variation.code.val,
  (argumentAt (.forkAfter (.copy a) (fst a a) (snd a a)) (2 : Fin 3)).variation.code.val)

/-- info: (2, 2, 17) -/
#guard_msgs in
#eval (stepCount (Track.comp (.step (Step.tensorLeft (copyStep a) (.copy b)))
    (.step (Step.tensorRight (fork (.identity a) (.identity a)) (copyStep b)))),
  stepCount (Track.comp (.step (Step.tensorRight (.copy a) (copyStep b)))
    (.step (Step.tensorLeft (copyStep a) (fork (.identity b) (.identity b))))),
  (Generator.tensorExchange (copyStep a) (copyStep b)).code.val)

def erasedEtaComparison (shape : Shape Atom) :=
  Homotopy.discardedParallel (beforeRule (Variation.eta shape shape shape) (copyStep shape))
    (afterRule (Variation.eta shape shape shape) (copyStep shape))

/-- info: (5, true) -/
#guard_msgs in
#eval (Homotopy.generatorCount (erasedEtaComparison a),
  decide (Homotopy.constructorCount (erasedEtaComparison a) ≤
    23 + 12 * (trackConstructorCount (beforeRule (.eta a a a) (copyStep a)) +
      trackConstructorCount (afterRule (.eta a a a) (copyStep a)))))

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.Examples

namespace CryptoLogic.Polygraph.MixedCircuit.Examples.CartesianHigher
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

def framedEta (stage : Nat) :=
  CartesianWiring.Higher.inContext (Placement.seqRight (MAC.before stage)) (Cartesian.Higher.Examples.etaCell MAC.finish)

theorem framedEta_support (stage : Nat) : PresentedCell.support (framedEta stage) = {stage} := by
  simp [framedEta, CartesianWiring.Higher.inContext_support, Placement.needs, MAC.before,
    Circuit.needs, MAC.signature, MACNormalization.layout]

def discardedEta (stage : Nat) :=
  (framedEta stage).whisker (Placement.seqLeft (.wire (.discard (.pair MAC.finish MAC.finish))))

theorem discardedEta_support (stage : Nat) : PresentedCell.support (discardedEta stage) = {stage} := by
  simp [discardedEta, PresentedCell.whisker_support, framedEta_support, Placement.needs, Circuit.needs]

theorem discardedEta_count (stage : Nat) : PresentedCell.constructorCount (discardedEta stage) = 1 := by
  rw [discardedEta, PresentedCell.whisker_constructorCount]
  simp [framedEta, CartesianWiring.Higher.inContext, PresentedCell.whisker_constructorCount,
    CartesianWiring.Higher.embedPure_constructorCount, Cartesian.Higher.Examples.etaCell,
    Cartesian.Higher.argumentCell, Cartesian.Higher.Homotopy.constructorCount]

theorem discardedEta_fresh (stage : Nat) : fresh (PresentedCell.support (discardedEta stage)) {stage + 1} = ∅ := by
  rw [discardedEta_support]
  simp [fresh]

/-- info: (1, 1, 0) -/
#guard_msgs in
#eval ((PresentedCell.support (discardedEta 0)).card, PresentedCell.constructorCount (discardedEta 0),
  (fresh (PresentedCell.support (discardedEta 0)) {1}).card)

/-- Keep the MAC result on the left; only the pure right branch is discarded. -/
def observedFrame (stage : Nat) :=
  CartesianWiring.Higher.inContext (Placement.tensorRight (MAC.before stage))
    (Cartesian.Higher.Examples.erasedEtaComparison MAC.finish)

theorem observedFrame_support (stage : Nat) : PresentedCell.support (observedFrame stage) = {stage} := by
  simp [observedFrame, CartesianWiring.Higher.inContext_support, Placement.needs,
    MAC.before, Circuit.needs, MAC.signature, MACNormalization.layout]

/-- info: 1 -/
#guard_msgs in
#eval (PresentedCell.support (observedFrame 0)).card

end CryptoLogic.Polygraph.MixedCircuit.Examples.CartesianHigher
