import Foundation.Constructions.Symmetric.EncryptThenMAC.NativePrivacyGame
import Foundation.Crypto.Logic.General.Execution

/-! Registration of the concrete privacy controller. Compiled syntax contains
only finite source instructions. Public inputs and CPU certificates are kept
in resources; neither the stopping bound nor a semantic decision tree is
compiled into the controller. This is the privacy half of EtM, not a complete
two-assumption operational realization. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
open CryptoLogic CryptoLogic.General Foundation.Probability CryptoOracle
open PrivacyGameCodec NativePrivacyGame
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Kind where
  | source | privacy
  deriving DecidableEq, Repr, Encodable

/-- The evaluator for this syntax is the fixed, cell-level privacy controller. -/
structure Compiled where
  source : Interactive.Code
  deriving Encodable

def Code : Kind → Type
  | .source => Interactive.Code
  | .privacy => Compiled

inductive Primitive : Kind → Kind → Type where
  | privacy : Primitive .source .privacy

def Primitive.decode (m n : Kind) (_ : Unit) : Option (Primitive m n) :=
  match m, n with
  | .source, .privacy => some .privacy
  | _, _ => none

instance (m n : Kind) : Encodable (Primitive m n) :=
  Encodable.ofLeftInjection (fun _ => ()) (Primitive.decode m n)
    (by intro p; cases p; rfl)

def system : CodeSystem where
  Machine := Kind
  Code := Code
  machineEncodable := inferInstance
  Primitive := Primitive
  codeEncodable := fun m => by cases m <;> dsimp [Code] <;> infer_instance
  primitiveEncodable := fun _ _ => inferInstance
  runPrimitive := fun p code => match p with
    | .privacy => ⟨code⟩

def compiler : Compiler system .source .privacy := .primitive .privacy

@[simp] theorem compiler_source (code : Interactive.Code) :
    (compiler.run code).source = code := rfl

/-- Resources describe public input and analysis fuel, never executable code. -/
structure Profile where
  count : Nat → Nat
  input : Nat → List Bool

noncomputable def privacyGoal (width : Nat → Nat) : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun n _ => PrivacyAttack OneBitEncryption.scheme (TableMAC.scheme width) n
  advantage := fun n _ A => probabilityGap
    (eventProb (privacyGame OneBitEncryption.scheme (TableMAC.scheme width) n false A) (· = true))
    (eventProb (privacyGame OneBitEncryption.scheme (TableMAC.scheme width) n true A) (· = true))

def SourceExecutes (width : Nat → Nat) (code : Interactive.Code) (r : Profile) : Prop :=
  PolynomiallyBounded width ∧ PolynomiallyBounded r.count ∧
    ∀ n side key, key ∈ (OneBitEncryption.scheme.keygen n).support →
      SourceStops width n key side code (r.count n) (r.input n)

def TargetExecutes (width : Nat → Nat) (code : Compiled) (r : Profile) : Prop :=
  PolynomiallyBounded (fun n => PrivacyMachine.executionBudget (width n) (r.count n)) ∧
    ∀ n side key, key ∈ (OneBitEncryption.scheme.keygen n).support →
      PrivacyMachine.HaltsWithin code.source (byteEncryptionOracle n key side)
        (PrivacyMachine.initial false (List.replicate (2 * width n) true) (r.input n))
        (PrivacyMachine.executionBudget (width n) (r.count n))

def SourceRealizes (width : Nat → Nat) (F : InstanceFamily (privacyGoal width))
    (A : AdversaryFamily (privacyGoal width) F) (code : Interactive.Code) (r : Profile) : Prop :=
  ∀ n, A n = attack width n code (r.count n) (r.input n)

def TargetRealizes (width : Nat → Nat) (F : InstanceFamily (encryptionGoal OneBitEncryption.scheme))
    (A : AdversaryFamily (encryptionGoal OneBitEncryption.scheme) F) (code : Compiled) (r : Profile) : Prop :=
  ∀ n side, game width n side code.source (r.count n) (r.input n) =
    encryptionGame OneBitEncryption.scheme n side (A n)

noncomputable def sourceObject (width : Nat → Nat) : SecurityObject system .source where
  goal := privacyGoal width
  execution := {
    Resources := Profile
    ExecutesWithin := fun _ code r => SourceExecutes width code r
    Realizes := SourceRealizes width }
  adversaries := { admissible := fun F A =>
    ∃ code r, SourceExecutes width code r ∧ SourceRealizes width F A code r }
  represented := by intro F A h; exact h

noncomputable def targetObject (width : Nat → Nat) : SecurityObject system .privacy where
  goal := encryptionGoal OneBitEncryption.scheme
  execution := {
    Resources := Profile
    ExecutesWithin := fun _ code r => TargetExecutes width code r
    Realizes := TargetRealizes width }
  adversaries := { admissible := fun F A =>
    ∃ code r, TargetExecutes width code r ∧ TargetRealizes width F A code r }
  represented := by intro F A h; exact h

theorem compiled_executes (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (h : SourceExecutes width code r) : TargetExecutes width (compiler.run code) r := by
  refine ⟨PrivacyMachine.execution_profile_polynomial h.1 h.2.1, ?_⟩
  intro n side key hKey
  exact NativePrivacyGame.halts width n key side code (r.count n) (r.input n) (h.2.2 n side key hKey)

noncomputable def transform (width : Nat → Nat) : AdversaryTransform (privacyGoal width) (encryptionGoal OneBitEncryption.scheme) :=
  ⟨fun _ => (), fun {n} _ A => privacyReduction OneBitEncryption.scheme (TableMAC.scheme width) n A⟩

theorem compiled_realizes (width : Nat → Nat) (F A) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (hReal : SourceRealizes width F A code r) :
    TargetRealizes width ((transform width).mapFamily F)
      ((transform width).mapAdversaryFamily F A) (compiler.run code) r := by
  intro n side
  change game width n side code (r.count n) (r.input n) =
    encryptionGame OneBitEncryption.scheme n side
      (privacyReduction OneBitEncryption.scheme (TableMAC.scheme width) n (A n))
  rw [hReal n]
  exact game_eq_encryption width n side code (r.count n) (r.input n) (hExec.2.2 n side)

/-- A concrete witness map, with genuine CPU stopping and game realization. -/
noncomputable def certificate (width : Nat → Nat) :
    CertifiedTransform (sourceObject width) (targetObject width) where
  transform := transform width
  compiler := compiler
  mapWitness := fun F A W => {
    code := compiler.run W.code
    resources := W.resources
    executes := compiled_executes width W.code W.resources W.executes
    realizes := compiled_realizes width F A W.code W.resources W.executes W.realizes
    admissible := ⟨compiler.run W.code, W.resources,
      compiled_executes width W.code W.resources W.executes,
      compiled_realizes width F A W.code W.resources W.executes W.realizes⟩ }
  code_eq := by intros; rfl

noncomputable def reduction (width : Nat → Nat) :
    Reduction (privacyGoal width) (encryptionGoal OneBitEncryption.scheme) where
  mapInstance := (transform width).mapInstance
  reduce := (transform width).reduce
  loss := AdvantageBound.id
  advantage_le := by
    intro n I A
    change probabilityGap
      (eventProb (privacyGame OneBitEncryption.scheme (TableMAC.scheme width) n false A) (· = true))
      (eventProb (privacyGame OneBitEncryption.scheme (TableMAC.scheme width) n true A) (· = true)) ≤
        probabilityGap
          (eventProb (encryptionGame OneBitEncryption.scheme n false
            (privacyReduction OneBitEncryption.scheme (TableMAC.scheme width) n A)) (· = true))
          (eventProb (encryptionGame OneBitEncryption.scheme n true
            (privacyReduction OneBitEncryption.scheme (TableMAC.scheme width) n A)) (· = true))
    rw [privacyGame_eq, privacyGame_eq]

/-- Quantitative cryptographic inference registered with finite compilation
and actual resource witnesses, rather than an operational interface alone. -/
noncomputable def certifiedReduction (width : Nat → Nat) :
    CertifiedReduction (sourceObject width) (targetObject width) where
  reduction := reduction width
  compiler := compiler
  mapWitness := (certificate width).mapWitness
  code_eq := (certificate width).code_eq
  negligible := AdvantageBound.id_preservesNegligible

@[simp] theorem certificate_resources (width : Nat → Nat) (F A)
    (W : (sourceObject width).Witness F A) :
    ((certificate width).mapWitness F A W).resources = W.resources := rfl

theorem certificate_time (width : Nat → Nat) (F A)
    (W : (sourceObject width).Witness F A) (n : Nat) :
    PrivacyMachine.executionBudget (width n)
      (((certificate width).mapWitness F A W).resources.count n) =
        12 * width n + 5 + W.resources.count n * (29 * width n + 39) := rfl

/-- Transfer a base-encryption security assumption using the represented
native attack classes and the concrete, polynomial-time witness map. -/
theorem secure (width : Nat → Nat) (F : InstanceFamily (privacyGoal width))
    (h : (targetObject width).Secure ((reduction width).mapFamily F)) :
    (sourceObject width).Secure F :=
  (certifiedReduction width).secure F h

end Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
