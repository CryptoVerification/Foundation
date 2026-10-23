import Foundation.Constructions.Symmetric.EncryptThenMAC.Translation
import Foundation.Logic.Polygraph.Translation
import Foundation.Logic.Polygraph.DiagramNormalization

/-! The authenticated-encryption macro expands to privacy, integrity, and
combination diagrams. The same translation preserves code, numerical loss,
and the complete dependent certificate model. No cryptographic conclusion is
introduced as an unproved generator. -/
namespace Foundation.Symmetric.EncryptThenMAC.Polygraph

open Foundation.Logic Foundation.Logic.Polygraph
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
universe v

def proof : Diagram Logic.higher Logic.context
    (Logic.Context.singleton ⟨Logic.Object.authenticated, Logic.Bound.add .encryption .mac⟩) :=
  Diagram.ofDerivation Logic.proof

def expand {Γ Δ : Foundation.Logic.Context Logic.higher} (d : Diagram Logic.higher Γ Δ) :=
  Translation.diagram Logic.expansion d

def expandedProof := Diagram.ofDerivation (Logic.expansion.translate Logic.proof)

def expansionPath : Diagram.Cell3 (expand proof) expandedProof :=
  Diagram.connect _ _ (by
    funext i
    simp [expand, proof, expandedProof, Translation.forest_diagram])

variable {K : CryptoLogic.General.CodeSystem} {auth enc mac : K.Machine}

theorem code_preserved (cE : CryptoLogic.General.Compiler K auth enc)
    (cM : CryptoLogic.General.Compiler K auth mac) (length : Nat)
    {Γ Δ : Foundation.Logic.Context Logic.higher} (d : Diagram Logic.higher Γ Δ)
    (env : Environment (Operational.higherCode cE cM length) Γ) (i : Fin Δ.length) :
    (expand d).eval (Operational.lowerCode cE cM length) env i =
      d.eval (Operational.higherCode cE cM length) env i :=
  Translation.eval_preserving Logic.expansion (Operational.codePreservation cE cM length) d env i

def lowerLoss : Model Logic.lower where
  Carrier := fun _ => ℝ≥0∞
  operation := fun rule children => match rule with
    | .privacy _ | .integrity _ => children 0
    | .combine _ _ => children 0 + children 1

def higherLoss : Model Logic.higher where
  Carrier := fun _ => ℝ≥0∞
  operation := fun _ children => children 0 + children 1

def lossPreservation : Model.Hom higherLoss (Logic.expansion.pullback lowerLoss) where
  map := fun _ value => value
  preserves := by intro rule children; cases rule; rfl

theorem loss_preserved {Γ Δ : Foundation.Logic.Context Logic.higher}
    (d : Diagram Logic.higher Γ Δ) (env : Environment higherLoss Γ) (i : Fin Δ.length) :
    (expand d).eval lowerLoss env i = d.eval higherLoss env i :=
  Translation.eval_preserving Logic.expansion lossPreservation d env i

theorem proof_loss (ε δ : ℝ≥0∞) :
    (expand proof).eval lowerLoss (Fin.cases ε (fun _ => δ)) 0 = ε + δ := by
  rw [loss_preserved]
  rfl

theorem proof_codes (cE : CryptoLogic.General.Compiler K auth enc)
    (cM : CryptoLogic.General.Compiler K auth mac) (code : K.Code auth) :
    (expand proof).eval (Operational.lowerCode cE cM 2)
      (fun i input => [(i, ⟨Operational.machine (Logic.context.claim i).object, input⟩)]) 0 code =
      [(0, ⟨enc, cE.run code⟩), (1, ⟨mac, cM.run code⟩)] := by
  rw [code_preserved]
  rfl

variable {E : Encryption} {M : MAC E.Ciphertext}
  {X : Operational.Backend.{v} K auth (goal E M)}
  {Y : Operational.Backend.{v} K enc (encryptionGoal E)}
  {Z : Operational.Backend.{v} K mac (macGoal E M)}
  {cE : CryptoLogic.General.Compiler K auth enc} {cM : CryptoLogic.General.Compiler K auth mac}

theorem witnesses_preserved (R : Operational.Realization X Y Z cE cM) (length : Nat)
    {Γ Δ : Foundation.Logic.Context Logic.higher} (d : Diagram Logic.higher Γ Δ)
    (env : Environment (Operational.higherWitnesses R length) Γ) (i : Fin Δ.length) :
    (expand d).eval (Operational.lowerWitnesses R length) env i =
      d.eval (Operational.higherWitnesses R length) env i :=
  Translation.eval_preserving Logic.expansion (Operational.witnessPreservation R length) d env i

theorem bounded (E : Encryption) (M : MAC E.Ciphertext)
    (CE : AdversaryClass (encryptionGoal E)) (CM : AdversaryClass (macGoal E M))
    (ε δ : Nat → ℝ≥0∞)
    (hE : BoundedByOnWithin (encryptionGoal E) CE (fun _ => ()) ε)
    (hM : BoundedByOnWithin (macGoal E M) CM (fun _ => ()) δ) :
    BoundedByOnWithin (goal E M) (sourceClass E M CE CM) (fun _ => ()) (fun n => ε n + δ n) := by
  have h := (expand proof).eval (Logic.model E M CE CM ε δ)
    (fun i => by fin_cases i; exact hE; exact hM) 0
  exact h

end Foundation.Symmetric.EncryptThenMAC.Polygraph
