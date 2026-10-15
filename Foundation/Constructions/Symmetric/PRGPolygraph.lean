import Foundation.Constructions.Symmetric.PRGPresented
import Foundation.Crypto.Logic.Polygraph.Resources
import Foundation.Crypto.Logic.Polygraph.Experiment
import Foundation.Logic.Polygraph.Occurrences

/-! A pure PRG-encryption diagram built from two computational replacements,
two exact uniform-pad rewrites, and the triangle inequality. The final
encryption theorem is not registered as a primitive inference rule. -/
namespace Foundation.Symmetric.Generator.Polygraph

open Foundation.Probability CryptoLogic.General CryptoLogic.General.Backends
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Object where
  | prg | masked (side : Bool) | half (side : Bool) | encryption
  deriving DecidableEq, Repr

def machine : Object → Kind
  | .prg => .masking
  | .masked _ | .half _ | .encryption => .native

inductive Unary : Object → Object → Type where
  | replace (side : Bool) : Unary (.masked side) .prg
  | uniform (side : Bool) : Unary (.half side) (.masked side)

inductive Binary : Object → Object → Object → Type where
  | triangle : Binary .encryption (.half false) (.half true)

abbrev language : CryptoLogic.General.Language system where
  Object := Object
  machine := machine
  Unary := Unary
  unaryCompiler := fun e => match e with
    | .replace side => .primitive (.mask side)
    | .uniform _ => Compiler.identity (K := system) Kind.native
  Binary := Binary
  binaryCompilers := fun e => match e with
    | .triangle => (Compiler.identity (K := system) Kind.native, Compiler.identity (K := system) Kind.native)

abbrev parameters : CryptoLogic.Presented.Parameters language where
  Family := fun _ => Unit
  unary := fun _ _ => ()
  left := fun _ _ => ()
  right := fun _ _ => ()

abbrev context : CryptoLogic.Presented.Context parameters :=
  Foundation.Logic.Context.singleton ⟨Object.prg, ()⟩

def branch (side : Bool) : CryptoLogic.Polygraph.Derivation parameters context (.half side) () :=
  CryptoLogic.Polygraph.Derivation.transport
    (P := parameters) (Γ := context)
    (.primitive (Unary.uniform side)) ()
    (CryptoLogic.Polygraph.Derivation.transport
      (P := parameters) (Γ := context)
      (.primitive (Unary.replace side)) ()
      (CryptoLogic.Polygraph.Derivation.hypothesis (P := parameters) (Γ := context) 0))

def proof : CryptoLogic.Polygraph.Derivation parameters context .encryption () :=
  CryptoLogic.Polygraph.Derivation.binary (P := parameters) (Γ := context)
    Binary.triangle () (branch false) (branch true)

/-- The unreduced ideal ciphertext is kept as a separate experiment. -/
noncomputable def idealPad (G : Generator) (n : Nat) (I : G.Messages n) (side : Bool) :=
  (G.ideal n).map (Bits.xor (G.message I side))

theorem idealPad_eq (G : Generator) (n : Nat) (I : G.Messages n) (side : Bool) :
    idealPad G n I side = G.ideal n := Bits.uniform_xor (G.message I side)

noncomputable def maskedGap (G : Generator) (side : Bool)
    (n : Nat) (I : G.Messages n) (A : G.Observer n) : ℝ≥0∞ :=
  probabilityGap (eventProb ((G.ciphertext n (G.message I side)).bind A) (· = true))
    (eventProb ((idealPad G n I side).bind A) (· = true))

noncomputable def halfGap (G : Generator) (side : Bool)
    (n : Nat) (I : G.Messages n) (A : G.Observer n) : ℝ≥0∞ :=
  probabilityGap (eventProb ((G.ciphertext n (G.message I side)).bind A) (· = true))
    (eventProb ((G.ideal n).bind A) (· = true))

/-- Computational replacement uses only the definition of the transformed
observer, not the equality of the ideal pad with uniform randomness. -/
theorem maskedGap_eq (G : Generator) (side : Bool) (n : Nat) (I : G.Messages n)
    (A : G.Observer n) :
    maskedGap G side n I A = G.prgGoal.advantage n I (G.reduce I side A) := by
  change probabilityGap _ _ = probabilityGap _ _
  rw [G.real_reduce]
  simp only [idealPad, PMF.bind_map]
  rfl

theorem halfGap_eq (G : Generator) (side : Bool) (n : Nat) (I : G.Messages n)
    (A : G.Observer n) : halfGap G side n I A = maskedGap G side n I A := by
  rw [maskedGap, idealPad_eq]
  rfl

noncomputable def object (G : Generator) (time : Nat → Nat) :
    ∀ X, CryptoLogic.General.SecurityObject.{0, 0} system (machine X)
  | .prg => prgMaskingObject G (G.reductionTime time)
  | .masked side => CryptoLogic.Polygraph.Experiment.observe (prgNativeObject G time)
      (maskedGap G side)
  | .half side => CryptoLogic.Polygraph.Experiment.observe (prgNativeObject G time)
      (halfGap G side)
  | .encryption => prgNativeObject G time

noncomputable def replacement (G : Generator) (time : Nat → Nat) (side : Bool) :
    CertifiedReduction (object G time (.masked side)) (object G time .prg) where
  reduction := {
    mapInstance := id
    reduce := fun I A => G.reduce I side A
    loss := AdvantageBound.id
    advantage_le := by
      intro n I A
      exact (maskedGap_eq G side n I A).le }
  compiler := .primitive (.mask side)
  mapWitness := fun F A W => (PRG.transform G time side).mapWitness F A
    ⟨W.code, W.resources, W.executes, W.realizes, W.admissible⟩
  code_eq := by intros; rfl
  negligible := AdvantageBound.id_preservesNegligible

noncomputable def uniformRewrite (G : Generator) (time : Nat → Nat) (side : Bool) :
    CertifiedReduction (object G time (.half side)) (object G time (.masked side)) where
  reduction := {
    mapInstance := id
    reduce := fun _ A => A
    loss := AdvantageBound.id
    advantage_le := by
      intro n I A
      exact (halfGap_eq G side n I A).le }
  compiler := Compiler.identity (K := system) Kind.native
  mapWitness := fun _ _ W => ⟨W.code, W.resources, W.executes, W.realizes, W.admissible⟩
  code_eq := by intros; rfl
  negligible := AdvantageBound.id_preservesNegligible

noncomputable def triangleBranch (G : Generator) (time : Nat → Nat) (side : Bool) :
    CertifiedTransform (object G time .encryption) (object G time (.half side)) where
  transform := ⟨id, fun _ A => A⟩
  compiler := Compiler.identity (K := system) Kind.native
  mapWitness := fun _ _ W => ⟨W.code, W.resources, W.executes, W.realizes, W.admissible⟩
  code_eq := by intros; rfl

noncomputable def triangle (G : Generator) (time : Nat → Nat) :
    CertifiedBinaryReduction (object G time .encryption)
      (object G time (.half false)) (object G time (.half true)) where
  left := triangleBranch G time false
  right := triangleBranch G time true
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

noncomputable def signature (G : Generator) (time : Nat → Nat) : Signature language where
  interpret := object G time
  unary := fun e => match e with
    | .replace side => replacement G time side
    | .uniform side => uniformRewrite G time side
  unary_compiler := by intro X Y e; cases e <;> rfl
  binary := fun e => match e with | .triangle => triangle G time
  left_compiler := by intro X Y Z e; cases e; rfl
  right_compiler := by intro X Y Z e; cases e; rfl

noncomputable def interpretation (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) :
    CryptoLogic.Presented.Interpretation parameters (signature G time) where
  family := fun {X} _ => match X with
    | .prg | .masked _ | .half _ | .encryption => F
  unary := by
    intro X Y r F'
    induction r with
    | identity X => rfl
    | primitive e => cases e <;> rfl
    | seq first second hf hs =>
        change _ = (second.eval (signature G time)).reduction.mapFamily
          ((first.eval (signature G time)).reduction.mapFamily _)
        rw [← hf, ← hs]
  left := by intro X Y Z e F'; cases e; rfl
  right := by intro X Y Z e F'; cases e; rfl

theorem occurrences : proof.occurrences.map Fin.val = [0, 0] := rfl

theorem run (program : Machine.Program) : CryptoLogic.Polygraph.Derivation.run proof program =
    [(0, ⟨Kind.masking, (reductionPrograms program).1⟩),
     (0, ⟨Kind.masking, (reductionPrograms program).2⟩)] := rfl

theorem loss (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Fin 1 → Nat → ℝ≥0∞) (n : Nat) :
    (CryptoLogic.Polygraph.Derivation.loss (interpretation G time F) proof).eval ε n =
      2 * ε 0 n := by
  change ε 0 n + ε 0 n = 2 * ε 0 n
  exact (two_mul _).symm

theorem bounded (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F ε) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass time) F (fun n => 2 * ε n) := by
  intro A hA n
  have bound := CryptoLogic.Polygraph.Derivation.bounded
    (interpretation G time F) proof (fun _ => ε) (fun _ => h) A hA n
  change advantageProfile G.encryptionGoal F A n ≤
    (CryptoLogic.Polygraph.Derivation.loss (interpretation G time F) proof).eval
      (fun _ => ε) n at bound
  simpa only [loss] using bound

theorem secure (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (h : SecureOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F) :
    SecureOnWithin G.encryptionGoal (G.nativeClass time) F :=
  CryptoLogic.Polygraph.Derivation.sound (interpretation G time F) proof (fun _ => h)

theorem runWitnesses_emitted (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (A) (W : G.NativeWitness time F A) :
    (CryptoLogic.Polygraph.Derivation.runWitnesses (interpretation G time F)
      proof A (PRG.nativeWitness W)).map CertifiedOutput.emitted =
    CryptoLogic.Polygraph.Derivation.run proof W.program :=
  CryptoLogic.Polygraph.Derivation.runWitnesses_emitted (interpretation G time F)
    proof A (PRG.nativeWitness W)

/-- Forget only the logical context packaging, retaining each target
adversary and its concrete all-challenge execution certificate. -/
noncomputable def targetWitnesses (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (A) (W : G.NativeWitness time F A) :
    List (Sigma fun B : AdversaryFamily G.prgGoal F =>
      G.ChallengeWitness (G.reductionTime time) F B) :=
  (CryptoLogic.Polygraph.Derivation.runWitnesses (interpretation G time F)
    proof A (PRG.nativeWitness W)).map fun out =>
    ⟨out.adversary, ⟨out.witness.code, out.witness.executes, out.witness.realizes⟩⟩

/-- The local proof emits precisely the established two operational
certificates, including their stopping and distribution-realization proofs. -/
theorem targetWitnesses_eq (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (A) (W : G.NativeWitness time F A) :
    targetWitnesses G time F A W =
      [⟨(fun n => G.reduce (F n) false (A n)), G.mapWitness time false F A W⟩,
       ⟨(fun n => G.reduce (F n) true (A n)), G.mapWitness time true F A W⟩] := rfl

theorem run_eq_presented (program : Machine.Program) :
    CryptoLogic.Polygraph.Derivation.run proof program =
      CryptoLogic.Presented.Derivation.run Presented.proof program := rfl

end Foundation.Symmetric.Generator.Polygraph
