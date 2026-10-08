import Foundation.Crypto.Meta.General.Metatheory
import Foundation.Examples.GeneralExecution
import Foundation.Examples.PRGLogic

/-! Concrete witnesses pass through the common API without erasing their
backend's resource predicates. Binary contraction retains both certificates. -/
namespace CryptoLogic.General.ResourceExamples

open Backends Foundation.Symmetric Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

-- One output retains native code, the other uses the masking controller.
example : (Examples.mixed.runWitnesses _ Examples.sourceWitness).map CertifiedOutput.emitted =
    [(0, ⟨Kind.native, [.randomBit .output, .halt]⟩),
     (1, ⟨Kind.masking, .masked true [.randomBit .output, .halt]⟩)] :=
  Examples.mixed.runWitnesses_emitted _ Examples.sourceWitness

-- The returned witness is over the precise family at its context position.
example (out : CertifiedOutput Examples.mixedContext) :
    (Examples.signature.interpret (Examples.mixedContext.claim out.index).object).execution.ExecutesWithin
      (Examples.mixedContext.claim out.index).family out.witness.code out.witness.resources :=
  out.witness.executes

example (out : CertifiedOutput Examples.mixedContext) :
    (Examples.signature.interpret (Examples.mixedContext.claim out.index).object).execution.Realizes
      (Examples.mixedContext.claim out.index).family out.adversary out.witness.code out.witness.resources :=
  out.witness.realizes

-- The same common API also returns the interactive whole-attack certificate.
example : (Examples.oracle.runWitnesses _ Examples.oracleWitness).map CertifiedOutput.emitted =
    [(0, ⟨Kind.interactive, CryptoOracle.Examples.adaptiveCode⟩)] :=
  Examples.oracle.runWitnesses_emitted _ Examples.oracleWitness

example : (Examples.oracle.runWitnesses _ Examples.oracleWitness).length = 1 := by
  rw [Examples.oracle.runWitnesses_length]
  rfl

noncomputable def prgWitness (G : Generator) (F : InstanceFamily G.encryptionGoal) :=
  PRG.nativeWitness (Foundation.Symmetric.Examples.randomWitness G F)

-- Sharing a single assumption preserves two independently certified programs.
example (G : Generator) (F : InstanceFamily G.encryptionGoal) :
    ((Generator.Logic.sharedDerivation G (fun _ => 2) F).runWitnesses _ (prgWitness G F)).map
      CertifiedOutput.emitted =
    [(0, ⟨Kind.masking, .masked false [.randomBit .output, .halt]⟩),
     (0, ⟨Kind.masking, .masked true [.randomBit .output, .halt]⟩)] := by
  rw [Derivation.runWitnesses_emitted]
  exact Generator.Logic.shared_run G (fun _ => 2) F _

example (G : Generator) (F : InstanceFamily G.encryptionGoal) :
    ((Generator.Logic.sharedDerivation G (fun _ => 2) F).runWitnesses _ (prgWitness G F)).length = 2 := by
  rw [Derivation.runWitnesses_length, Generator.Logic.shared_run]
  rfl

example (G : Generator) (F : InstanceFamily G.encryptionGoal) :
    (Generator.Logic.sharedDerivation G (fun _ => 2) F).runWitnesses _ (prgWitness G F) ≠ [] :=
  Derivation.runWitnesses_ne_nil _ _ _

-- Explicit analyses preserve the selected loss after substituting hypotheses.
example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Fin 1 → Nat → ℝ≥0∞) (n : Nat) :
    (Generator.Logic.sharedAnalysis G t F).loss.eval ε n = 2 * ε 0 n :=
  Generator.Logic.shared_loss_eval G t F ε n

example (G : Generator) (F : InstanceFamily G.encryptionGoal) :
    ((Generator.Logic.sharedAnalysis G (fun _ => 2) F).runWitnesses _ (prgWitness G F)).map
      CertifiedOutput.emitted =
    [(0, ⟨Kind.masking, .masked false [.randomBit .output, .halt]⟩),
     (0, ⟨Kind.masking, .masked true [.randomBit .output, .halt]⟩)] := by
  rw [Derivation.Analysis.runWitnesses_emitted]
  exact Generator.Logic.shared_run G (fun _ => 2) F _

-- One concrete negligible bound implies asymptotic security inside precisely
-- the fixed resource class; this does not quantify over all running times.
example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Nat → ℝ≥0∞)
    (h : (prgMaskingObject G (G.reductionTime t)).Bounded F ε) (hε : Negligible ε) :
    (prgNativeObject G t).Secure F :=
  Generator.Logic.secure G t F (h.asymptotic hε)

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal) :
    Nonempty (Derivation (Generator.Logic.signature G t) (Generator.Logic.context G t F)
      Generator.Logic.Object.encryption F) ↔
    Nonempty (Tree (Generator.Logic.signature G t) (Generator.Logic.context G t F)
      Generator.Logic.Object.encryption F) := derivable_iff_registered_tree

end CryptoLogic.General.ResourceExamples
