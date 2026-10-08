import Foundation.Constructions.Symmetric.PRGLogic

/-! One fixed syntactic proof, interpreted at any generator, time bound, and
public message family. The proof and its code generator do not receive any of
those semantic arguments. Two uses of one PRG assumption stay distinct. -/
namespace Foundation.Symmetric.Generator.Presented

open CryptoLogic.General CryptoLogic.General.Backends
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev parameters := Logic.pureParameters
abbrev twoContext := Logic.pureContext

abbrev context : CryptoLogic.Presented.Context parameters where
  length := 1
  claim _ := ⟨Logic.Object.prg, ()⟩

abbrev twoProof := Logic.presentedDerivation

def proof : CryptoLogic.Presented.Derivation parameters context Logic.Object.encryption () :=
  twoProof.substitute fun _ =>
    Foundation.Logic.Derivation.hypothesis (T := CryptoLogic.Presented.presentation parameters) (Γ := context) 0

noncomputable abbrev interpretation (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) := Logic.familyInterpretation G time F

theorem run (program : Machine.Program) : CryptoLogic.Presented.Derivation.run proof program =
    [(0, ⟨Kind.masking, (reductionPrograms program).1⟩),
     (0, ⟨Kind.masking, (reductionPrograms program).2⟩)] := rfl

theorem interpreted_tree (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) :
    (interpretation G time F).tree proof = (Logic.sharedAnalysis G time F).tree := rfl

theorem loss (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Fin 1 → Nat → ℝ≥0∞) (n : Nat) :
    ((interpretation G time F).loss proof).eval ε n = 2 * ε 0 n := by
  change ε 0 n + ε 0 n = 2 * ε 0 n
  exact (two_mul _).symm

theorem bounded (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F ε) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass time) F (fun n => 2 * ε n) := by
  intro A hA n
  have hb := (interpretation G time F).bounded proof (fun _ => ε) (fun _ => h) A hA n
  change advantageProfile G.encryptionGoal F A n ≤
    ((interpretation G time F).loss proof).eval (fun _ => ε) n at hb
  simpa only [loss] using hb

theorem secure (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (h : SecureOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F) :
    SecureOnWithin G.encryptionGoal (G.nativeClass time) F :=
  (interpretation G time F).sound proof (fun _ => h)

theorem runWitnesses (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (A) (W : G.NativeWitness time F A) :
    ((interpretation G time F).runWitnesses proof A (PRG.nativeWitness W)).map CryptoLogic.General.CertifiedOutput.emitted =
      CryptoLogic.Presented.Derivation.run proof W.program :=
  (interpretation G time F).runWitnesses_emitted proof A (PRG.nativeWitness W)

end Foundation.Symmetric.Generator.Presented
