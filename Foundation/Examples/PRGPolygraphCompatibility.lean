import Foundation.Constructions.Symmetric.PRGPresented
import Foundation.Crypto.Logic.Polygraph.Resources
import Foundation.Logic.Polygraph.Occurrences

/-! Compatibility checkpoint only: this example uses the existing composite
encryption rule. It checks diagram extraction against the established PRG
proof; it is not the planned construction from local experiment rewrites. -/
namespace Foundation.Symmetric.Generator.PolygraphCompatibility

open CryptoLogic.General CryptoLogic.General.Backends
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def proof : CryptoLogic.Polygraph.Derivation Presented.parameters Presented.context
    Logic.Object.encryption () :=
  CryptoLogic.Polygraph.Derivation.binary (P := Presented.parameters) (Γ := Presented.context)
    Logic.Binary.encryption ()
    (CryptoLogic.Polygraph.Derivation.hypothesis (P := Presented.parameters) (Γ := Presented.context) 0)
    (CryptoLogic.Polygraph.Derivation.hypothesis (P := Presented.parameters) (Γ := Presented.context) 0)

theorem toPresented : CryptoLogic.Polygraph.Derivation.toPresented proof = Presented.proof := by
  apply congrArg (Foundation.Logic.Derivation.apply
    (T := CryptoLogic.Presented.presentation Presented.parameters) (Γ := Presented.context)
    (CryptoLogic.Presented.Rule.binary Logic.Binary.encryption ()))
  funext i
  exact Fin.cases rfl (fun k => Fin.cases rfl (fun z => Fin.elim0 z) k) i

/-- Two occurrences stay attached to the same hypothesis index. -/
theorem occurrences : proof.occurrences.map Fin.val = [0, 0] := rfl

theorem run (program : Machine.Program) : CryptoLogic.Polygraph.Derivation.run proof program =
    [(0, ⟨Kind.masking, (reductionPrograms program).1⟩),
     (0, ⟨Kind.masking, (reductionPrograms program).2⟩)] := rfl

theorem loss (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Fin 1 → Nat → ℝ≥0∞) (n : Nat) :
    (CryptoLogic.Polygraph.Derivation.loss (Presented.interpretation G time F) proof).eval ε n =
      2 * ε 0 n := Presented.loss G time F ε n

theorem bounded (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F ε) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass time) F (fun n => 2 * ε n) := by
  intro A hA n
  have bound := CryptoLogic.Polygraph.Derivation.bounded
    (Presented.interpretation G time F) proof (fun _ => ε) (fun _ => h) A hA n
  change advantageProfile G.encryptionGoal F A n ≤
    (CryptoLogic.Polygraph.Derivation.loss (Presented.interpretation G time F) proof).eval
      (fun _ => ε) n at bound
  simpa only [loss] using bound

/-- Equality of the entire certificate list, not merely the emitted codes. -/
theorem runWitnesses (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (A) (W : G.NativeWitness time F A) :
    CryptoLogic.Polygraph.Derivation.runWitnesses (Presented.interpretation G time F)
      proof A (PRG.nativeWitness W) =
    (Presented.interpretation G time F).runWitnesses Presented.proof A (PRG.nativeWitness W) := rfl

end Foundation.Symmetric.Generator.PolygraphCompatibility
