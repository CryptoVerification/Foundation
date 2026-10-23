import Foundation.Logic.Polygraph.StructuralTransport
import Foundation.Crypto.Semantics.Probability.Copyability
import Foundation.Examples.RandomFunctionMACAutomaticEdit

/-! Structural editing of the already sampled complete MAC record. A nested
copy/discard/tensor/swap circuit is reduced by explicit elementary cells.
The decoded result retains two identical full records, not two independent
runs. Independent reruns are provably different even on the actual labels. -/
namespace Foundation.Symmetric.RandomFunctionMACStructuralTransport
open Foundation.Probability Foundation.Logic.Polygraph.StructuralTransport
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACScopedEdit (repairedFamily repairedGame)
open RandomFunctionMACRepresentationSwitch (oldCodec)

abbrev Changed := Representation.Switch.Retained (Fin 8) (Fin 256) Bool (Fin 256) Bool (Bits 8)
abbrev Original := Representation.Switch.Retained (Fin 8) (Fin 256) Bool (Fin 256) Bool (Fin 256)
abbrev ChangedFamily : Unit → Type := fun _ => Changed
abbrev OriginalFamily : Unit → Type := fun _ => Original

def decoder : Changed → Original := Representation.Switch.decode oldCodec
  (Representation.GeneratedEdit.codecs repairedFamily RandomFunctionMACNativeCaller.Backend.tagEquiv)

def maps (_ : Unit) : Changed → Original := decoder

def recordShape : Shape Unit := .atom ()

def forgetExtra : Wire recordShape recordShape :=
  .seq (.seq (.copy recordShape) (.tensor (.discard recordShape) (.identity recordShape))) (.leftUnit recordShape)

def forgetCell : Cell forgetExtra (.identity recordShape) := .copyDiscardLeft recordShape

def view : Wire recordShape (.pair recordShape recordShape) :=
  .seq (.copy recordShape)
    (.seq (.tensor forgetExtra (.identity recordShape)) (.swap recordShape recordShape))

/-- Explicit structural pasting, with no semantic-equality generator. -/
def viewCell : Cell view (.copy recordShape) :=
  (Cell.seq (.refl (.copy recordShape))
    (.seq (.tensor forgetCell (.refl (.identity recordShape))) (.refl (.swap recordShape recordShape)))).trans
  ((Cell.seq (.refl (.copy recordShape))
    (.seq (.tensorIdentity recordShape recordShape) (.refl (.swap recordShape recordShape)))).trans
  ((Cell.seq (.refl (.copy recordShape)) (.seqLeftUnit (.swap recordShape recordShape))).trans
    (.copySwap recordShape)))

theorem view_evaluation (value : Changed) : view.eval ChangedFamily value = (value, value) :=
  viewCell.sound ChangedFamily value

theorem decoded_source : repairedGame.map decoder = RandomFunctionMACRepresentationSwitch.original :=
  RandomFunctionMACScopedEdit.local_repair_sound.2

theorem decoded_view :
    (repairedGame.map (view.eval ChangedFamily)).map (fun pair => (decoder pair.1, decoder pair.2)) =
      Copyability.shared RandomFunctionMACRepresentationSwitch.original := by
  have transported := view.transport maps repairedGame
  change (repairedGame.map (view.eval ChangedFamily)).map (fun pair => (decoder pair.1, decoder pair.2)) =
    (repairedGame.map decoder).map (view.eval OriginalFamily) at transported
  rw [decoded_source] at transported
  exact transported.trans (viewCell.distribution OriginalFamily RandomFunctionMACRepresentationSwitch.original)

theorem final_game :
    ((repairedGame.map (view.eval ChangedFamily)).map (fun pair => (decoder pair.1, decoder pair.2))).map
      (fun pair => pair.1.2.2) = RandomFunctionMACNativeCaller.target.run RandomOracle.oracle [] := by
  rw [decoded_view]
  simpa only [Copyability.shared, PMF.map_comp, Function.comp_def] using
    RandomFunctionMACRepresentationSwitch.original_game

theorem original_selection : RandomFunctionMACRepresentationSwitch.original.map (fun value => value.2.1) = uniform Bool := by
  have projected := congrArg (fun law : PMF Original => law.map (fun value => value.2.1))
    RandomFunctionMACRepresentationSwitch.decoded_joint
  simp only [PMF.map_comp, Function.comp_def, Representation.Switch.decode] at projected
  exact projected.symm.trans RandomFunctionMACRepresentationSwitch.selection_law

theorem actual_selection : repairedGame.map (fun value => value.2.1) = uniform Bool := by
  have projected := congrArg (fun law : PMF Original => law.map (fun value => value.2.1)) decoded_source
  simp only [PMF.map_comp, Function.comp_def, decoder, Representation.Switch.decode] at projected
  exact projected.trans original_selection

theorem shared_selection_agreement :
    eventProb (Copyability.shared repairedGame) (fun pair => pair.1.2.1 = pair.2.2.1) = 1 := by
  have law := Copyability.shared_map repairedGame (fun value : Changed => value.2.1)
  rw [actual_selection] at law
  have observed := eventProb_map (Copyability.shared repairedGame)
    (fun pair => (pair.1.2.1, pair.2.2.1)) (fun pair => pair.1 = pair.2)
  rw [law] at observed
  exact observed.symm.trans (Copyability.shared_agreement (uniform Bool))

theorem independent_selection_agreement :
    eventProb (Copyability.independent repairedGame repairedGame) (fun pair => pair.1.2.1 = pair.2.2.1) = 1 / 2 := by
  have law := Copyability.independent_map repairedGame repairedGame
    (fun value : Changed => value.2.1) (fun value : Changed => value.2.1)
  rw [actual_selection] at law
  have observed := eventProb_map (Copyability.independent repairedGame repairedGame)
    (fun pair => (pair.1.2.1, pair.2.2.1)) (fun pair => pair.1 = pair.2)
  rw [law] at observed
  exact observed.symm.trans Copyability.fair_independent_agreement

theorem copy_is_not_rerun : Copyability.shared repairedGame ≠ Copyability.independent repairedGame repairedGame := by
  intro equal
  have projected := congrArg (fun law : PMF (Changed × Changed) =>
    law.map (fun pair => (pair.1.2.1, pair.2.2.1))) equal
  change (Copyability.shared repairedGame).map (fun pair => ((fun value : Changed => value.2.1) pair.1,
      (fun value : Changed => value.2.1) pair.2)) = _ at projected
  have one := Copyability.shared_map repairedGame (fun value : Changed => value.2.1)
  have two := Copyability.independent_map repairedGame repairedGame
    (fun value : Changed => value.2.1) (fun value : Changed => value.2.1)
  have labels := one.symm.trans (projected.trans two)
  rw [actual_selection] at labels
  exact Copyability.fair_not_copyable labels

/-- info: ((true, true), 7) -/
#guard_msgs in
#eval (view.eval (fun _ : Unit => Bool) true, forgetExtra.eval (fun _ : Unit => Nat) (7 : Nat))

end Foundation.Symmetric.RandomFunctionMACStructuralTransport
