import Foundation.Constructions.Symmetric.PRGPresented
import Foundation.Examples.PRGLogic
import Foundation.Examples.CounterWhole
import Foundation.Crypto.Logic.General.Legacy
import Foundation.Examples.PureLogic

/-! Executable syntax without a security interpretation, repeated assumptions,
multiple models, and preservation of whole interactive execution certificates. -/
namespace Foundation.Symmetric.PresentedExamples

open CryptoLogic.General CryptoLogic.General.Backends
open Generator
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

-- No generator, time bound, message family, or semantic signature is passed.
/-- info: true -/
#guard_msgs in
#eval LogicExamples.programs (CryptoLogic.Presented.Derivation.run
  Presented.proof Examples.testProgram) ==
  [(0, .masked false Examples.testProgram), (0, .masked true Examples.testProgram)]

-- The same proof admits two independently chosen interpretations. Both keep
-- the exact emitted code, even when their execution bounds differ.
example (G H : Generator) (t s : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (E : InstanceFamily H.encryptionGoal)
    (p : Machine.Program) :
    ((Presented.interpretation G t F).legacy Presented.proof).run p =
      ((Presented.interpretation H s E).legacy Presented.proof).run p := by
  rw [CryptoLogic.Presented.Interpretation.legacy_run,
    CryptoLogic.Presented.Interpretation.legacy_run]

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime t)) F ε) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass t) F (fun n => 2 * ε n) :=
  Presented.bounded G t F ε h

-- This is an equality of whole certificates, not just their code fields.
example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (A) (W : G.NativeWitness t F A) :
    (Presented.interpretation G t F).runWitnesses Presented.proof A (PRG.nativeWitness W) =
      (Logic.sharedAnalysis G t F).runWitnesses A (PRG.nativeWitness W) := by
  change (Derivation.ofTreeAnalysis ((Presented.interpretation G t F).tree Presented.proof)).runWitnesses
    A (PRG.nativeWitness W) = _
  rw [Presented.interpreted_tree]
  rfl

-- Pullbacks can also be actual syntax rather than semantic family functions.
abbrev symbolicParameters := CryptoLogic.Presented.symbolicParameters
  (L := Logic.language) (fun _ => Unit)
abbrev symbolicFamily : CryptoLogic.Presented.FamilyExpr
    (L := Logic.language) (fun _ => Unit) Logic.Object.encryption := .atom ()
abbrev symbolicContext : CryptoLogic.Presented.Context symbolicParameters where
  length := 2
  claim := Fin.cases ⟨Logic.Object.prg, .left Logic.Binary.encryption symbolicFamily⟩
    (fun _ => ⟨Logic.Object.prg, .right Logic.Binary.encryption symbolicFamily⟩)

def symbolicProof : CryptoLogic.Presented.Derivation symbolicParameters symbolicContext
    Logic.Object.encryption symbolicFamily :=
  CryptoLogic.Presented.Derivation.binary (P := symbolicParameters) (Γ := symbolicContext)
    Logic.Binary.encryption symbolicFamily
    (Foundation.Logic.Derivation.hypothesis (T := CryptoLogic.Presented.presentation symbolicParameters)
      (Γ := symbolicContext) 0)
    (Foundation.Logic.Derivation.hypothesis (T := CryptoLogic.Presented.presentation symbolicParameters)
      (Γ := symbolicContext) 1)

example (p : Machine.Program) : CryptoLogic.Presented.Derivation.run symbolicProof p =
    [(0, ⟨Kind.masking, .masked false p⟩), (1, ⟨Kind.masking, .masked true p⟩)] := rfl

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal) :
    (CryptoLogic.Presented.FamilyExpr.interpretation (Logic.signature G t)
      (fun X _ => match X with | .encryption => F | .prg => F)).family symbolicFamily = F := rfl

end Foundation.Symmetric.PresentedExamples

namespace CryptoOracle.CounterWholeExamples

open CryptoLogic.General Foundation.Symmetric.PRFCounter Foundation.Symmetric.PRFCounter.Resource
set_option backward.isDefEq.respectTransparency false

-- An adaptive, two-query native attack is reconstructed with its original
-- resource values, stopping proofs, and distribution realizations intact.
example :
    (CryptoLogic.Presented.interpretation (Logic.signature adaptiveScheme adaptiveTime adaptiveAllowance)).runWitnesses
      (CryptoLogic.Presented.quote (Logic.sharedAnalysis adaptiveScheme adaptiveTime adaptiveAllowance).tree)
      (fun _ => adaptiveTyped) adaptiveWitness =
    (Derivation.ofTreeAnalysis (Logic.sharedAnalysis adaptiveScheme adaptiveTime adaptiveAllowance).tree).runWitnesses
      (fun _ => adaptiveTyped) adaptiveWitness :=
  CryptoLogic.Presented.quote_runWitnesses _ _ _

end CryptoOracle.CounterWholeExamples
