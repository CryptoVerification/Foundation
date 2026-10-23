import Foundation.Constructions.Symmetric.PRGOptimized
import Foundation.Constructions.Symmetric.PRGPolygraph
import Foundation.Crypto.Meta.Polygraph.CartesianCoherence

/-! The optimized controller is interpreted by the same local PRG proof:
computational replacement, ideal-pad equality, and triangle. A new finite
code tag selects the proved implementation; security is never introduced as
one primitive rule. Full target witnesses carry the smaller resource bound. -/
namespace Foundation.Symmetric.Generator.Optimized.Polygraph
open Foundation.Probability
open CryptoLogic.General
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev Object := Generator.Polygraph.Object
abbrev Unary := Generator.Polygraph.Unary
abbrev Binary := Generator.Polygraph.Binary

def machine : Object → Bool
  | .prg => true
  | .masked _ | .half _ | .encryption => false

abbrev language : CryptoLogic.General.Language system where
  Object := Object
  machine := machine
  Unary := Unary
  unaryCompiler := fun e => match e with
    | .replace side => .primitive (.mask .fused side)
    | .uniform _ => Compiler.identity (K := system) false
  Binary := Binary
  binaryCompilers := fun e => match e with
    | .triangle => (Compiler.identity (K := system) false, Compiler.identity (K := system) false)

abbrev parameters : CryptoLogic.Presented.Parameters language where
  Family := fun _ => Unit
  unary := fun _ _ => ()
  left := fun _ _ => ()
  right := fun _ _ => ()

abbrev context : CryptoLogic.Presented.Context parameters :=
  Foundation.Logic.Context.singleton ⟨Generator.Polygraph.Object.prg, ()⟩

def branch (side : Bool) : CryptoLogic.Polygraph.Derivation parameters context (.half side) () :=
  CryptoLogic.Polygraph.Derivation.transport
    (P := parameters) (Γ := context)
    (.primitive (Generator.Polygraph.Unary.uniform side)) ()
    (CryptoLogic.Polygraph.Derivation.transport
      (P := parameters) (Γ := context)
      (.primitive (Generator.Polygraph.Unary.replace side)) ()
      (CryptoLogic.Polygraph.Derivation.hypothesis (P := parameters) (Γ := context) 0))

def proof : CryptoLogic.Polygraph.Derivation parameters context .encryption () :=
  CryptoLogic.Polygraph.Derivation.binary (P := parameters) (Γ := context)
    Generator.Polygraph.Binary.triangle () (branch false) (branch true)

noncomputable abbrev maskedGap := Generator.Polygraph.maskedGap
noncomputable abbrev halfGap := Generator.Polygraph.halfGap
abbrev maskedGap_eq := Generator.Polygraph.maskedGap_eq
abbrev halfGap_eq := Generator.Polygraph.halfGap_eq

noncomputable def object (G : Generator) (time : Nat → Nat)
    (_ht : PolynomiallyBounded time) (_hL : PolynomiallyBounded G.outputLength) :
    ∀ X, CryptoLogic.General.SecurityObject.{0, 0} system (machine X)
  | .prg => (target G).refine (fun _ _ r => ∀ n, r n ≤ Optimized.time G time n)
  | .masked side => CryptoLogic.Polygraph.Experiment.observe (source G time) (maskedGap G side)
  | .half side => CryptoLogic.Polygraph.Experiment.observe (source G time) (halfGap G side)
  | .encryption => source G time

noncomputable def replacement (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength) (side : Bool) :
    CertifiedReduction (object G time ht hL (.masked side)) (object G time ht hL .prg) where
  reduction := {
    mapInstance := id
    reduce := fun I A => G.reduce I side A
    loss := AdvantageBound.id
    advantage_le := by intro n I A; exact (maskedGap_eq G side n I A).le }
  compiler := .primitive (.mask .fused side)
  mapWitness := fun F A W => (tight G time ht hL side).mapWitness F A
    ⟨W.code, W.resources, W.executes, W.realizes, W.admissible⟩
  code_eq := by intros; rfl
  negligible := AdvantageBound.id_preservesNegligible

noncomputable def uniformRewrite (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength) (side : Bool) :
    CertifiedReduction (object G time ht hL (.half side)) (object G time ht hL (.masked side)) where
  reduction := {
    mapInstance := id
    reduce := fun _ A => A
    loss := AdvantageBound.id
    advantage_le := by
      intro n I A
      exact (halfGap_eq G side n I A).le }
  compiler := Compiler.identity (K := system) false
  mapWitness := fun _ _ W => ⟨W.code, W.resources, W.executes, W.realizes, W.admissible⟩
  code_eq := by intros; rfl
  negligible := AdvantageBound.id_preservesNegligible

noncomputable def triangleBranch (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength) (side : Bool) :
    CertifiedTransform (object G time ht hL .encryption) (object G time ht hL (.half side)) where
  transform := ⟨id, fun _ A => A⟩
  compiler := Compiler.identity (K := system) false
  mapWitness := fun _ _ W => ⟨W.code, W.resources, W.executes, W.realizes, W.admissible⟩
  code_eq := by intros; rfl

noncomputable def triangle (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength) :
    CertifiedBinaryReduction (object G time ht hL .encryption)
      (object G time ht hL (.half false)) (object G time ht hL (.half true)) where
  left := triangleBranch G time ht hL false
  right := triangleBranch G time ht hL true
  leftLoss := AdvantageBound.id
  rightLoss := AdvantageBound.id
  leftNegligible := AdvantageBound.id_preservesNegligible
  rightNegligible := AdvantageBound.id_preservesNegligible
  advantage_le := by
    intro F A n
    have h := CryptoLogic.ThreeGames.probabilityGap_triangle
      (eventProb ((G.ciphertext n (F n).1).bind (A n)) (· = true))
      (eventProb ((G.ideal n).bind (A n)) (· = true))
      (eventProb ((G.ciphertext n (F n).2).bind (A n)) (· = true))
    change probabilityGap
      (eventProb ((G.ciphertext n (F n).1).bind (A n)) (· = true))
      (eventProb ((G.ciphertext n (F n).2).bind (A n)) (· = true)) ≤
      probabilityGap
        (eventProb ((G.ciphertext n (F n).1).bind (A n)) (· = true))
        (eventProb ((G.ideal n).bind (A n)) (· = true)) +
      probabilityGap
        (eventProb ((G.ciphertext n (F n).2).bind (A n)) (· = true))
        (eventProb ((G.ideal n).bind (A n)) (· = true))
    simpa only [probabilityGap, max_comm] using h

noncomputable def signature (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength) : Signature language where
  interpret := object G time ht hL
  unary := fun e => match e with
    | .replace side => replacement G time ht hL side
    | .uniform side => uniformRewrite G time ht hL side
  unary_compiler := by intro X Y e; cases e <;> rfl
  binary := fun e => match e with | .triangle => triangle G time ht hL
  left_compiler := by intro X Y Z e; cases e; rfl
  right_compiler := by intro X Y Z e; cases e; rfl

noncomputable def interpretation (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength)
    (F : InstanceFamily G.encryptionGoal) :
    CryptoLogic.Presented.Interpretation parameters (signature G time ht hL) where
  family := fun {X} _ => match X with
    | .prg | .masked _ | .half _ | .encryption => F
  unary := by
    intro X Y r F'
    induction r with
    | identity X => rfl
    | primitive e => cases e <;> rfl
    | seq first second hf hs =>
        change _ = (second.eval (signature G time ht hL)).reduction.mapFamily
          ((first.eval (signature G time ht hL)).reduction.mapFamily _)
        rw [← hf, ← hs]
  left := by intro X Y Z e F'; cases e; rfl
  right := by intro X Y Z e F'; cases e; rfl

theorem run (program : Machine.Program) : CryptoLogic.Polygraph.Derivation.run proof program =
    [(0, ⟨true, (.fused, Machine.Masking.compile false program)⟩),
     (0, ⟨true, (.fused, Machine.Masking.compile true program)⟩)] := rfl

theorem loss (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength)
    (F : InstanceFamily G.encryptionGoal) (ε : Fin 1 → Nat → ℝ≥0∞) (n : Nat) :
    (CryptoLogic.Polygraph.Derivation.loss (interpretation G time ht hL F) proof).eval ε n =
      2 * ε 0 n := by
  change ε 0 n + ε 0 n = 2 * ε 0 n
  exact (two_mul _).symm

theorem bounded (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength)
    (F : InstanceFamily G.encryptionGoal) (ε : Nat → ℝ≥0∞)
    (h : (object G time ht hL .prg).Bounded F ε) :
    (object G time ht hL .encryption).Bounded F (fun n => 2 * ε n) := by
  intro A hA n
  have bound := CryptoLogic.Polygraph.Derivation.bounded
    (interpretation G time ht hL F) proof (fun _ => ε) (fun _ => h) A hA n
  change advantageProfile G.encryptionGoal F A n ≤
    (CryptoLogic.Polygraph.Derivation.loss (interpretation G time ht hL F) proof).eval
      (fun _ => ε) n at bound
  change advantageProfile G.encryptionGoal F A n ≤ 2 * ε n
  simpa only [loss] using bound

theorem resource_profiles (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength)
    (F : InstanceFamily G.encryptionGoal) (A) (W : (source G time).Witness F A) :
    (CryptoLogic.Polygraph.Derivation.runWitnesses (interpretation G time ht hL F)
      proof A W).map (fun out => out.witness.resources) =
        [Optimized.time G time, Optimized.time G time] := rfl

theorem output_constraints (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength)
    (F : InstanceFamily G.encryptionGoal) (A) (W : (source G time).Witness F A) :
    ∀ out ∈ CryptoLogic.Polygraph.Derivation.runWitnesses (interpretation G time ht hL F) proof A W,
      ∀ n, out.witness.resources n ≤ Optimized.time G time n := by
  intro out _
  exact out.witness.executes.2

def wrapped := Foundation.Logic.Polygraph.Diagram.seq (.identity context) proof

def unitPath : Foundation.Logic.Polygraph.Diagram.Cell3 wrapped proof := .step (.leftUnit proof)
def reconstructionPath : Foundation.Logic.Polygraph.Diagram.Cell3 wrapped proof :=
  Foundation.Logic.Polygraph.Diagram.connect _ _ unitPath.forest_eq

def comparison : Foundation.Logic.Polygraph.Cartesian.Cell4 unitPath reconstructionPath :=
  Foundation.Logic.Polygraph.Cartesian.coherent _ _

theorem witnesses_path (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength)
    (F : InstanceFamily G.encryptionGoal) (A) (W : (source G time).Witness F A) :
    CryptoLogic.Polygraph.Derivation.runWitnesses (interpretation G time ht hL F) wrapped A W =
      CryptoLogic.Polygraph.Derivation.runWitnesses (interpretation G time ht hL F) proof A W :=
  CryptoLogic.Polygraph.Derivation.witnesses_path unitPath (interpretation G time ht hL F) A W

end Foundation.Symmetric.Generator.Optimized.Polygraph
