import Foundation.Crypto.Logic.General.Backends
import Foundation.Crypto.Meta.General.ResourceSecurity

/-! Registration of one-time PRG encryption in the machine-independent logic.
Both premises are PRG distinguishing goals with the original public messages.
The source uses native bit code; both targets use the finite XOR controller.
The inference retains the two occurrences even when one assumption is reused. -/
namespace Foundation.Symmetric.Generator.Logic

open CryptoLogic.General CryptoLogic.General.Backends
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

inductive Object where
  | encryption | prg
  deriving DecidableEq, Repr

def machine : Object → Kind
  | .encryption => .native
  | .prg => .masking

inductive Binary : Object → Object → Object → Type where
  | encryption : Binary .encryption .prg .prg

abbrev language : Language system where
  Object := Object
  machine := machine
  Unary := fun _ _ => PEmpty
  unaryCompiler := fun e => nomatch e
  Binary := Binary
  binaryCompilers := fun e => match e with
    | .encryption => (.primitive (.mask false), .primitive (.mask true))

/-- The registered binary inference uses the operationally certified
compilers and the previously proved sum of the two PRG advantages. -/
noncomputable def certificate (G : Generator) (time : Nat → Nat) :
    CertifiedBinaryReduction (prgNativeObject G time)
      (prgMaskingObject G (G.reductionTime time))
      (prgMaskingObject G (G.reductionTime time)) where
  left := PRG.transform G time false
  right := PRG.transform G time true
  leftLoss := AdvantageBound.id
  rightLoss := AdvantageBound.id
  leftNegligible := AdvantageBound.id_preservesNegligible
  rightNegligible := AdvantageBound.id_preservesNegligible
  advantage_le := by intro F A n; exact G.advantage_le n (F n) (A n)

noncomputable def signature (G : Generator) (time : Nat → Nat) : Signature language where
  interpret := fun X => match X with
    | .encryption => prgNativeObject G time
    | .prg => prgMaskingObject G (G.reductionTime time)
  unary := fun e => nomatch e
  unary_compiler := fun e => nomatch e
  binary := fun e => match e with | .encryption => certificate G time
  left_compiler := by intro X Y Z e; cases e; rfl
  right_compiler := by intro X Y Z e; cases e; rfl

/-- Two positions permit distinct bounds for the two reductions. The
underlying security assertion and public instance family are identical. -/
@[macro_inline] def context (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) : Context (signature G time) where
  length := 2
  claim _ := ⟨Object.prg, F⟩

@[macro_inline] def derivation (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) :
    Derivation (signature G time) (context G time F) Object.encryption F :=
  Derivation.binary (S := signature G time) (Γ := context G time F) Binary.encryption F
    (Derivation.hypothesis (S := signature G time) (Γ := context G time F) ⟨0, by change 0 < 2; decide⟩)
    (Derivation.hypothesis (S := signature G time) (Γ := context G time F) ⟨1, by change 1 < 2; decide⟩)

/-- The explicit semantic tree accompanies exactly the pure emitted plan. -/
noncomputable def tree (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) :
    Tree (signature G time) (context G time F) Object.encryption F :=
  Tree.binary (S := signature G time) (Γ := context G time F) Binary.encryption F
    (Tree.hypothesis (S := signature G time) (Γ := context G time F) ⟨0, by change 0 < 2; decide⟩)
    (Tree.hypothesis (S := signature G time) (Γ := context G time F) ⟨1, by change 1 < 2; decide⟩)

theorem tree_plan (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal) :
    (tree G time F).plan = (derivation G time F).plan := rfl

/-- Fix the registered tree used for resource and loss analysis. No choice
between possible certificates changes the caller's selected loss expression. -/
noncomputable def analysis (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) : Derivation.Analysis (derivation G time F) :=
  ⟨tree G time F, tree_plan G time F⟩

theorem run (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (program : Machine.Program) :
    (derivation G time F).run program =
      [(0, ⟨Kind.masking, (reductionPrograms program).1⟩),
       (1, ⟨Kind.masking, (reductionPrograms program).2⟩)] := rfl

/-- Substitution reuses one PRG assumption twice, without merging the code
or the loss of the two independently executable reductions. -/
@[macro_inline] def sharedContext (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) : Context (signature G time) where
  length := 1
  claim _ := ⟨Object.prg, F⟩

@[macro_inline] def sharedDerivation (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) :
    Derivation (signature G time) (sharedContext G time F) Object.encryption F :=
  (derivation G time F).substitute fun _ =>
    Derivation.hypothesis (S := signature G time) (Γ := sharedContext G time F) ⟨0, by change 0 < 1; decide⟩

noncomputable def sharedAnalysis (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) : Derivation.Analysis (sharedDerivation G time F) :=
  (analysis G time F).substitute
    (fun _ => Derivation.hypothesis (S := signature G time) (Γ := sharedContext G time F)
      ⟨0, by change 0 < 1; decide⟩)
    (fun _ => ⟨Tree.hypothesis (S := signature G time) (Γ := sharedContext G time F)
      ⟨0, by change 0 < 1; decide⟩, rfl⟩)

theorem shared_loss_eval (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (ε : Fin 1 → Nat → ℝ≥0∞) (n : Nat) :
    (sharedAnalysis G time F).loss.eval ε n = 2 * ε 0 n := by
  change ε 0 n + ε 0 n = 2 * ε 0 n
  rw [two_mul]

theorem shared_run (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (program : Machine.Program) :
    (sharedDerivation G time F).run program =
      [(0, ⟨Kind.masking, (reductionPrograms program).1⟩),
       (0, ⟨Kind.masking, (reductionPrograms program).2⟩)] := rfl

/-- Security is derived through the general soundness theorem, including
reuse of the one PRG hypothesis at both leaves. -/
theorem secure (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (h : SecureOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F) :
    SecureOnWithin G.encryptionGoal (G.nativeClass time) F := by
  apply (sharedDerivation G time F).sound
  intro i
  exact h

/-- The registered tree's loss is the sum, with no extra multiplicative
factor hidden in either branch. -/
theorem loss_eval (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Fin 2 → Nat → ℝ≥0∞) (n : Nat) :
    (tree G time F).loss.eval ε n = ε 0 n + ε 1 n := rfl

/-- Concrete security is a specialization of general tree extraction,
using the same tree whose plan emits the two certified programs. -/
theorem bounded (G : Generator) (time : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε₀ ε₁ : Nat → ℝ≥0∞)
    (h₀ : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F ε₀)
    (h₁ : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F ε₁) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass time) F (fun n => ε₀ n + ε₁ n) := by
  let ε : Fin 2 → Nat → ℝ≥0∞ := fun i => if i.val = 0 then ε₀ else ε₁
  have hε : ∀ i : Fin 2, BoundedByOnWithin G.prgGoal
      (G.challengeClass (G.reductionTime time)) F (ε i) := by
    intro i
    dsimp [ε]
    split_ifs
    · exact h₀
    · exact h₁
  intro A hA n
  have h := (analysis G time F).bounded ε hε A hA n
  change advantageProfile G.encryptionGoal F A n ≤ (tree G time F).loss.eval ε n at h
  simpa only [loss_eval, ε, Fin.val_zero, Fin.val_one, ite_true, ite_false,
    Nat.zero_ne_one, Nat.one_ne_zero] using h

theorem bounded_twice (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F ε) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass time) F (fun n => 2 * ε n) := by
  intro A hA n
  have hb := (sharedAnalysis G time F).bounded (fun _ => ε) (fun _ => h) A hA n
  change advantageProfile G.encryptionGoal F A n ≤
    (sharedAnalysis G time F).loss.eval (fun _ => ε) n at hb
  simpa only [shared_loss_eval] using hb


/-- Each listed output has the whole-runtime and realization certificate
provided by the general extraction theorem, for precisely the emitted code. -/
theorem extract_emitted (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (program : Machine.Program) :
    (derivation G time F).extract.map (fun leaf => (leaf.index.val, (leaf.emitted program).2)) =
      [(0, ⟨Kind.masking, .masked false program⟩),
       (1, ⟨Kind.masking, .masked true program⟩)] :=
  (derivation G time F).extract_emitted program

theorem shared_extract_emitted (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (program : Machine.Program) :
    (sharedDerivation G time F).extract.map (fun leaf => (leaf.index.val, (leaf.emitted program).2)) =
      [(0, ⟨Kind.masking, .masked false program⟩),
       (0, ⟨Kind.masking, .masked true program⟩)] :=
  (sharedDerivation G time F).extract_emitted program

/-- The actual emitted masking code halts at the certified whole-runtime
bound, for every length-correct challenge and every native coin branch. -/
theorem emitted_halts (G : Generator) (time : Nat → Nat) (side : Bool)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A) (n : Nat) (challenge : Bits (G.outputLength n)) :
    Machine.Masking.HaltsWithin (Machine.Masking.compile side W.program)
      (Machine.Masking.initial (Machine.Masking.compile side W.program)
        (G.header n (F n)) (F n).1.toList (F n).2.toList challenge.toList)
      (G.reductionTime time n) := by
  cases side with
  | false => exact (certificate G time).left.compiler_executes F A (PRG.nativeWitness W) n challenge
  | true => exact (certificate G time).right.compiler_executes F A (PRG.nativeWitness W) n challenge

/-- The emitted code realizes each semantic branch on every challenge.
This is the general execution interface's exact distribution equality. -/
theorem emitted_output (G : Generator) (time : Nat → Nat) (side : Bool)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A) (n : Nat) (challenge : Bits (G.outputLength n)) :
    Machine.Masking.output (Machine.Masking.compile side W.program)
      (Machine.Masking.initial (Machine.Masking.compile side W.program)
        (G.header n (F n)) (F n).1.toList (F n).2.toList challenge.toList)
      (G.reductionTime time n) = (G.reduce (F n) side (A n) challenge).map some := by
  cases side with
  | false => exact (certificate G time).left.compiler_realizes F A (PRG.nativeWitness W) n challenge
  | true => exact (certificate G time).right.compiler_realizes F A (PRG.nativeWitness W) n challenge

/-- Full result-and-trace equality for any challenge distribution, obtained
from the general certified compiler's pointwise realization theorem. -/
theorem emitted_realizes (G : Generator) (time : Nat → Nat) (side : Bool)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A) (n : Nat)
    (distribution : Foundation.Probability.ProbComp (Bits (G.outputLength n))) :
    runChallenge distribution (fun challenge =>
      Machine.Masking.output (Machine.Masking.compile side W.program)
        (Machine.Masking.initial (Machine.Masking.compile side W.program) (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) (G.reductionTime time n)) =
    runChallenge distribution (fun challenge => (G.reduce (F n) side (A n) challenge).map some) := by
  unfold runChallenge
  congr 1
  funext challenge
  exact congrArg (fun p : Foundation.Probability.ProbComp (Option Bool) =>
    p.map (fun result => (⟨result, [challenge]⟩ : ChallengeOutcome (G.outputLength n) (Option Bool))))
    (emitted_output G time side F A W n challenge)

/-- One challenge acquisition per branch is a property of every outcome
in the complete experiment, which also records the challenge itself. -/
theorem emitted_queries (G : Generator) (time : Nat → Nat) (side : Bool)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A) (n : Nat)
    (distribution : Foundation.Probability.ProbComp (Bits (G.outputLength n)))
    (outcome : ChallengeOutcome (G.outputLength n) (Option Bool))
    (h : outcome ∈ (runChallenge distribution (fun challenge =>
      Machine.Masking.output (Machine.Masking.compile side W.program)
        (Machine.Masking.initial (Machine.Masking.compile side W.program) (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) (G.reductionTime time n))).support) :
    outcome.trace.length = 1 := runChallenge_queries _ _ outcome h

end Foundation.Symmetric.Generator.Logic
