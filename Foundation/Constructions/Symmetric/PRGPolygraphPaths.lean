import Foundation.Constructions.Symmetric.PRGPolygraph
import Foundation.Crypto.Meta.Polygraph.Normalization
import Foundation.Crypto.Logic.Polygraph.ExperimentSyntax

/-! The existing local PRG proof uses the general experiment/path APIs.
Uniform-pad equality is a distribution transformation; computational
replacement retains its masking compiler and its complete witness map. -/
namespace Foundation.Symmetric.Generator.Polygraph

open CryptoLogic.Polygraph
open CryptoLogic.General CryptoLogic.General.Backends

noncomputable def idealPadPath (G : Generator) (n : Nat) (I : G.Messages n) (side : Bool) :
    Experiment.ExactPath (.sample (idealPad G n I side)) (.sample (G.ideal n)) :=
  .step (.distribution (idealPad_eq G n I side))

noncomputable def replacementPath (G : Generator) (time : Nat → Nat) (side : Bool) :
    Experiment.ComputationalPath (object G time (.masked side)) (object G time .prg) :=
  .reduction (replacement G time side)

def normalizedProof := Derivation.normalize proof

def normalizationPath : Derivation.StructuralPath proof normalizedProof :=
  Derivation.normalizePath proof

theorem normalized_run (code : _root_.Machine.Program) :
    Derivation.run normalizedProof code = Derivation.run proof code :=
  Derivation.normalize_run proof code

theorem normalized_loss (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal) :
    Derivation.loss (interpretation G time F) normalizedProof =
      Derivation.loss (interpretation G time F) proof :=
  Derivation.normalize_loss proof (interpretation G time F)

theorem normalized_witnesses (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal) (A)
    (W : (object G time .encryption).Witness F A) :
    Derivation.runWitnesses (interpretation G time F) normalizedProof A W =
      Derivation.runWitnesses (interpretation G time F) proof A W :=
  Derivation.normalize_witnesses proof (interpretation G time F) A W

end Foundation.Symmetric.Generator.Polygraph
