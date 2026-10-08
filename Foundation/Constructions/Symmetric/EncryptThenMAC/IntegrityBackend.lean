import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeIntegrityGame
import Foundation.Crypto.Logic.General.Execution

/-! Registration of the concrete integrity controller: finite source code,
real CPU stopping certificates, and the actual MAC signing transcript. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
open CryptoLogic CryptoLogic.General Foundation.Probability CryptoOracle
open IntegrityGameCodec IntegrityGameObservation NativeIntegrityGame
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Kind where
  | source | integrity
  deriving DecidableEq, Repr, Encodable

/-- The evaluator for this syntax is the fixed, cell-level integrity controller. -/
structure Compiled where
  source : Interactive.Code
  deriving Encodable

def Code : Kind → Type
  | .source => Interactive.Code
  | .integrity => Compiled

inductive Primitive : Kind → Kind → Type where
  | integrity : Primitive .source .integrity

def Primitive.decode (m n : Kind) (_ : Unit) : Option (Primitive m n) :=
  match m, n with
  | .source, .integrity => some .integrity
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
    | .integrity => ⟨code⟩

def compiler : Compiler system .source .integrity := .primitive .integrity

@[simp] theorem compiler_source (code : Interactive.Code) :
    (compiler.run code).source = code := rfl

/-- Resources describe public input and analysis fuel, never executable code. -/
structure Profile where
  count : Nat → Nat
  input : Nat → List Bool

noncomputable def integrityGoal (width : Nat → Nat) : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun n _ => IntegrityAttack OneBitEncryption.scheme (TableMAC.scheme width) n
  advantage := fun n _ A => integrityAdvantage OneBitEncryption.scheme (TableMAC.scheme width) n A


def SourceExecutes (width : Nat → Nat) (code : Interactive.Code) (r : Profile) : Prop :=
  PolynomiallyBounded width ∧ PolynomiallyBounded r.count ∧
    ∀ n macKey, macKey ∈ ((TableMAC.scheme width).keygen n).support →
      SourceStops width n macKey code (r.count n) (r.input n)

def TargetExecutes (width : Nat → Nat) (code : Compiled) (r : Profile) : Prop :=
  PolynomiallyBounded (fun n => IntegrityMachine.executionBudget (width n) (r.count n)) ∧
    ∀ n macKey, macKey ∈ ((TableMAC.scheme width).keygen n).support →
      IntegrityMachine.HaltsWithin code.source (byteSigningOracle macKey)
        (IntegrityMachine.initial () (r.input n))
        (IntegrityMachine.executionBudget (width n) (r.count n))

def SourceRealizes (width : Nat → Nat) (F : InstanceFamily (integrityGoal width))
    (A : AdversaryFamily (integrityGoal width) F) (code : Interactive.Code) (r : Profile) : Prop :=
  ∀ n, A n = attack width n code (r.count n) (r.input n)

def TargetRealizes (width : Nat → Nat) (F : InstanceFamily (macGoal OneBitEncryption.scheme (TableMAC.scheme width)))
    (A : AdversaryFamily (macGoal OneBitEncryption.scheme (TableMAC.scheme width)) F) (code : Compiled) (r : Profile) : Prop :=
  ∀ n, game width n code.source (r.count n) (r.input n) =
    macGame OneBitEncryption.scheme (TableMAC.scheme width) n (A n)

noncomputable def sourceObject (width : Nat → Nat) : SecurityObject system .source where
  goal := integrityGoal width
  execution := {
    Resources := Profile
    ExecutesWithin := fun _ code r => SourceExecutes width code r
    Realizes := SourceRealizes width }
  adversaries := { admissible := fun F A =>
    ∃ code r, SourceExecutes width code r ∧ SourceRealizes width F A code r }
  represented := by intro F A h; exact h

noncomputable def targetObject (width : Nat → Nat) : SecurityObject system .integrity where
  goal := macGoal OneBitEncryption.scheme (TableMAC.scheme width)
  execution := {
    Resources := Profile
    ExecutesWithin := fun _ code r => TargetExecutes width code r
    Realizes := TargetRealizes width }
  adversaries := { admissible := fun F A =>
    ∃ code r, TargetExecutes width code r ∧ TargetRealizes width F A code r }
  represented := by intro F A h; exact h

theorem compiled_executes (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (h : SourceExecutes width code r) : TargetExecutes width (compiler.run code) r := by
  refine ⟨IntegrityMachine.execution_profile_polynomial h.1 h.2.1, ?_⟩
  intro n macKey hKey
  exact IntegrityGameObservation.execution_halts width n macKey code (r.count n) (r.input n) (h.2.2 n macKey hKey)

noncomputable def transform (width : Nat → Nat) : AdversaryTransform (integrityGoal width) (macGoal OneBitEncryption.scheme (TableMAC.scheme width)) :=
  ⟨fun _ => (), fun {n} _ A => integrityReduction OneBitEncryption.scheme (TableMAC.scheme width) n A⟩

theorem compiled_realizes (width : Nat → Nat) (F A) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (hReal : SourceRealizes width F A code r) :
    TargetRealizes width ((transform width).mapFamily F)
      ((transform width).mapAdversaryFamily F A) (compiler.run code) r := by
  intro n
  change game width n code (r.count n) (r.input n) =
    macGame OneBitEncryption.scheme (TableMAC.scheme width) n
      (integrityReduction OneBitEncryption.scheme (TableMAC.scheme width) n (A n))
  rw [hReal n]
  exact game_eq width n code (r.count n) (r.input n) (hExec.2.2 n)

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
    Reduction (integrityGoal width) (macGoal OneBitEncryption.scheme (TableMAC.scheme width)) where
  mapInstance := (transform width).mapInstance
  reduce := (transform width).reduce
  loss := AdvantageBound.id
  advantage_le := by
    intro n I A
    exact integrity_advantage_le OneBitEncryption.scheme (TableMAC.scheme width) n A

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
    IntegrityMachine.executionBudget (width n)
      (((certificate width).mapWitness F A W).resources.count n) =
        3 + W.resources.count n * (5 * width n + 36) := rfl

/-- Transfer a base-MAC security assumption using the represented
native attack classes and the concrete, polynomial-time witness map. -/
theorem secure (width : Nat → Nat) (F : InstanceFamily (integrityGoal width))
    (h : (targetObject width).Secure ((reduction width).mapFamily F)) :
    (sourceObject width).Secure F :=
  (certifiedReduction width).secure F h

end Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
