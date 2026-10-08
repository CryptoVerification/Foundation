import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyBackend
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityBackend
import Foundation.Constructions.Symmetric.EncryptThenMAC.Translation

/-! A concrete two-assumption backend. Each source consists of two finite
attack programs, and compilation selects the corresponding fixed controller.
All CPU and game witnesses are constructed from the proved native executions. -/
namespace Foundation.Symmetric.EncryptThenMAC.ConcreteOperational
open CryptoLogic.General CryptoOracle
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Kind where
  | authenticated | encryption | mac
  deriving DecidableEq, Repr, Encodable

abbrev SourceCode := Interactive.Code × Interactive.Code

def Code : Kind → Type
  | .authenticated => SourceCode
  | .encryption => PrivacyBackend.Compiled
  | .mac => IntegrityBackend.Compiled

inductive Primitive : Kind → Kind → Type where
  | encryption : Primitive .authenticated .encryption
  | mac : Primitive .authenticated .mac

def Primitive.decode (m n : Kind) (_ : Unit) : Option (Primitive m n) :=
  match m, n with
  | .authenticated, .encryption => some .encryption
  | .authenticated, .mac => some .mac
  | _, _ => none

instance (m n : Kind) : Encodable (Primitive m n) :=
  Encodable.ofLeftInjection (fun _ => ()) (Primitive.decode m n)
    (by intro p; cases p <;> rfl)

def system : CodeSystem where
  Machine := Kind
  Code := Code
  machineEncodable := inferInstance
  Primitive := Primitive
  codeEncodable := fun m => by cases m <;> dsimp [Code] <;> infer_instance
  primitiveEncodable := fun _ _ => inferInstance
  runPrimitive := fun p code => match p with
    | .encryption => ⟨code.1⟩
    | .mac => ⟨code.2⟩

def encryptionCompiler : Compiler system .authenticated .encryption := .primitive .encryption
def macCompiler : Compiler system .authenticated .mac := .primitive .mac

abbrev Profile := PrivacyBackend.Profile × IntegrityBackend.Profile

def SourceExecutes (width : Nat → Nat) (code : SourceCode) (r : Profile) : Prop :=
  PrivacyBackend.SourceExecutes width code.1 r.1 ∧
  IntegrityBackend.SourceExecutes width code.2 r.2

def SourceRealizes (width : Nat → Nat)
    (F : InstanceFamily (goal OneBitEncryption.scheme (TableMAC.scheme width)))
    (A : AdversaryFamily (goal OneBitEncryption.scheme (TableMAC.scheme width)) F)
    (code : SourceCode) (r : Profile) : Prop :=
  (∀ n, (A n).1 = PrivacyGameCodec.attack width n code.1 (r.1.count n) (r.1.input n)) ∧
  (∀ n, (A n).2 = IntegrityGameCodec.attack width n code.2 (r.2.count n) (r.2.input n))

noncomputable def sourceBackend (width : Nat → Nat) :
    Operational.Backend system .authenticated (goal OneBitEncryption.scheme (TableMAC.scheme width)) where
  execution := {
    Resources := Profile
    ExecutesWithin := fun _ code r => SourceExecutes width code r
    Realizes := SourceRealizes width }
  adversaries := { admissible := fun F A =>
    ∃ code r, SourceExecutes width code r ∧ SourceRealizes width F A code r }
  represented := by intro F A h; exact h

noncomputable def encryptionBackend (width : Nat → Nat) :
    Operational.Backend system .encryption (encryptionGoal OneBitEncryption.scheme) where
  execution := {
    Resources := PrivacyBackend.Profile
    ExecutesWithin := fun _ code r => PrivacyBackend.TargetExecutes width code r
    Realizes := PrivacyBackend.TargetRealizes width }
  adversaries := (PrivacyBackend.targetObject width).adversaries
  represented := (PrivacyBackend.targetObject width).represented

noncomputable def macBackend (width : Nat → Nat) :
    Operational.Backend system .mac (macGoal OneBitEncryption.scheme (TableMAC.scheme width)) where
  execution := {
    Resources := IntegrityBackend.Profile
    ExecutesWithin := fun _ code r => IntegrityBackend.TargetExecutes width code r
    Realizes := IntegrityBackend.TargetRealizes width }
  adversaries := (IntegrityBackend.targetObject width).adversaries
  represented := (IntegrityBackend.targetObject width).represented

noncomputable def encryptionWitness (width : Nat → Nat) (F A)
    (W : (sourceBackend width).object.Witness F A) :
    (encryptionBackend width).object.Witness (fun _ => ())
      (fun n => privacyReduction OneBitEncryption.scheme (TableMAC.scheme width) n (A n).1) := by
  have he := PrivacyBackend.compiled_executes width W.code.1 W.resources.1 W.executes.1
  have hr : PrivacyBackend.TargetRealizes width (fun _ => ())
      (fun n => privacyReduction OneBitEncryption.scheme (TableMAC.scheme width) n (A n).1)
      (PrivacyBackend.compiler.run W.code.1) W.resources.1 := by
    intro n side
    change NativePrivacyGame.game width n side W.code.1 (W.resources.1.count n) (W.resources.1.input n) = _
    dsimp only
    rw [W.realizes.1 n]
    exact NativePrivacyGame.game_eq_encryption width n side W.code.1
      (W.resources.1.count n) (W.resources.1.input n) (W.executes.1.2.2 n side)
  exact {
    code := encryptionCompiler.run W.code
    resources := W.resources.1
    executes := he
    realizes := hr
    admissible := ⟨PrivacyBackend.compiler.run W.code.1, W.resources.1, he, hr⟩ }

noncomputable def macWitness (width : Nat → Nat) (F A)
    (W : (sourceBackend width).object.Witness F A) :
    (macBackend width).object.Witness (fun _ => ())
      (fun n => integrityReduction OneBitEncryption.scheme (TableMAC.scheme width) n (A n).2) := by
  have he := IntegrityBackend.compiled_executes width W.code.2 W.resources.2 W.executes.2
  have hr : IntegrityBackend.TargetRealizes width (fun _ => ())
      (fun n => integrityReduction OneBitEncryption.scheme (TableMAC.scheme width) n (A n).2)
      (IntegrityBackend.compiler.run W.code.2) W.resources.2 := by
    intro n
    change NativeIntegrityGame.game width n W.code.2 (W.resources.2.count n) (W.resources.2.input n) = _
    dsimp only
    rw [W.realizes.2 n]
    exact NativeIntegrityGame.game_eq width n W.code.2
      (W.resources.2.count n) (W.resources.2.input n) (W.executes.2.2.2 n)
  exact {
    code := macCompiler.run W.code
    resources := W.resources.2
    executes := he
    realizes := hr
    admissible := ⟨IntegrityBackend.compiler.run W.code.2, W.resources.2, he, hr⟩ }

/-- Both native witness maps discharge the operational interface. -/
noncomputable def realization (width : Nat → Nat) :
    Operational.Realization (sourceBackend width) (encryptionBackend width) (macBackend width)
      encryptionCompiler macCompiler where
  encryptionWitness := encryptionWitness width
  macWitness := macWitness width
  encryptionCode := by intros; rfl
  macCode := by intros; rfl

noncomputable def certificate (width : Nat → Nat) := (realization width).certificate

@[simp] theorem encryption_resources (width : Nat → Nat) (F A)
    (W : (sourceBackend width).object.Witness F A) :
    ((realization width).encryptionWitness F A W).resources = W.resources.1 := rfl

@[simp] theorem mac_resources (width : Nat → Nat) (F A)
    (W : (sourceBackend width).object.Witness F A) :
    ((realization width).macWitness F A W).resources = W.resources.2 := rfl

/-- Each output uses its own CPU units and source execution profile. -/
theorem execution_bounds (width : Nat → Nat) (F A)
    (W : (sourceBackend width).object.Witness F A) (n : Nat) :
    PrivacyMachine.executionBudget (width n)
      (((realization width).encryptionWitness F A W).resources.count n) =
      12 * width n + 5 + W.resources.1.count n * (29 * width n + 39) ∧
    IntegrityMachine.executionBudget (width n)
      (((realization width).macWitness F A W).resources.count n) =
      3 + W.resources.2.count n * (5 * width n + 36) := ⟨rfl, rfl⟩

/-- The translated macro emits the two actual finite controller programs. -/
theorem translated_codes (code : SourceCode) :
    (Operational.plan encryptionCompiler macCompiler (Logic.expansion.translate Logic.proof)).run code =
      [(0, ⟨Kind.encryption, PrivacyBackend.Compiled.mk code.1⟩),
       (1, ⟨Kind.mac, IntegrityBackend.Compiled.mk code.2⟩)] :=
  Operational.proof_plan encryptionCompiler macCompiler code

/-- Translation preserves the complete native execution witnesses. -/
theorem translated_witnesses (width : Nat → Nat)
    (A : AdversaryFamily (goal OneBitEncryption.scheme (TableMAC.scheme width)) (fun _ => ()))
    (W : (sourceBackend width).object.Witness (fun _ => ()) A) :
    (Operational.proofWitnesses (realization width) A W).map Operational.WitnessOutput.emitted =
      (Operational.plan encryptionCompiler macCompiler (Logic.expansion.translate Logic.proof)).run W.code :=
  Operational.proof_witnesses_plan (realization width) A W

/-- The quantitative semantic theorem now applies to actual represented code. -/
theorem bounded (width : Nat → Nat) (ε δ : Nat → ℝ≥0∞)
    (hE : BoundedByOnWithin (encryptionGoal OneBitEncryption.scheme)
      (encryptionBackend width).adversaries (fun _ => ()) ε)
    (hM : BoundedByOnWithin (macGoal OneBitEncryption.scheme (TableMAC.scheme width))
      (macBackend width).adversaries (fun _ => ()) δ) :
    BoundedByOnWithin (goal OneBitEncryption.scheme (TableMAC.scheme width))
      (sourceBackend width).adversaries (fun _ => ()) (fun n => ε n + δ n) :=
  (realization width).bounded ε δ hE hM

theorem secure (width : Nat → Nat) (F)
    (hE : (encryptionBackend width).object.Secure ((certificate width).left.transform.mapFamily F))
    (hM : (macBackend width).object.Secure ((certificate width).right.transform.mapFamily F)) :
    (sourceBackend width).object.Secure F :=
  (certificate width).secure F hE hM

end Foundation.Symmetric.EncryptThenMAC.ConcreteOperational
