import Foundation.Logic.Polygraph.FiniteCompletion
import Foundation.Crypto.Meta.Polygraph.Normalization

/-! The finite schematic coherence basis acts on cryptographic diagrams.
Every route preserves exactly the emitted codes, chosen loss expression, and
full execution certificate list in its original backend-specific types. -/
namespace CryptoLogic.Polygraph.FiniteCoherence

open General
open Foundation.Logic.Polygraph
universe u v a b p
set_option linter.checkUnivs false

def interpretPath {T : Foundation.Logic.Presentation} {Γ Δ : Foundation.Logic.Context T}
    {f g : Diagram.Composition T Γ Δ} (path : Composition.Finite.Three f g) :
    Diagram.Cell3 (Diagram.denoteComposition f) (Diagram.denoteComposition g) :=
  path.map (S := fun x y => Diagram.StructuralStep x y) Diagram.denoteComposition
    (fun s => Diagram.compositionStep s)

variable {K : CodeSystem} {L : General.Language.{a, b} K}
  {P : Presented.Parameters.{a, b, p} L} {Γ : Presented.Context P}
  {S : General.Signature.{u, v} L} {X F}
  {f g : Diagram.Composition (Presented.presentation P) Γ
    (Foundation.Logic.Context.singleton ⟨X, F⟩)}

theorem run_path (path : Composition.Finite.Three f g) (code : K.Code (L.machine X)) :
    Derivation.run (Diagram.denoteComposition f) code =
      Derivation.run (Diagram.denoteComposition g) code :=
  Derivation.run_path (interpretPath path) code

theorem loss_path (path : Composition.Finite.Three f g) (M : Presented.Interpretation P S) :
    Derivation.loss M (Diagram.denoteComposition f) = Derivation.loss M (Diagram.denoteComposition g) :=
  Derivation.loss_path (interpretPath path) M

theorem witnesses_path (path : Composition.Finite.Three f g) (M : Presented.Interpretation P S)
    (A) (W : (S.interpret X).Witness (M.family F) A) :
    Derivation.runWitnesses M (Diagram.denoteComposition f) A W =
      Derivation.runWitnesses M (Diagram.denoteComposition g) A W :=
  Derivation.witnesses_path (interpretPath path) M A W

end CryptoLogic.Polygraph.FiniteCoherence
