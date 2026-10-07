import Foundation.Constructions.Symmetric.EncryptThenMAC.ConcreteOperational
import Foundation.Constructions.Symmetric.EncryptThenMAC.OneBitSecurity
import Foundation.Constructions.Symmetric.EncryptThenMAC.TableMACSecurity

/-! Unconditional quantitative security of the concrete one-use composition.
The base assumptions of the translated rule are discharged by proved exact
privacy and a one-query information-theoretic MAC bound. -/
namespace Foundation.Symmetric.EncryptThenMAC.ConcreteSecurity
open Foundation.Probability CryptoOracle CryptoLogic.General ConcreteOperational
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Width zero is allowed and gives the vacuous, correct probability bound 1. -/
noncomputable def tagGuessBound (width : Nat → Nat) (n : Nat) : ℝ≥0∞ := (2 ^ (width n) : ℝ≥0∞)⁻¹

/-- The semantic composition theorem is instantiated with proved base bounds. -/
theorem semantic_bound (width : Nat → Nat) (n : Nat)
    (attack : Attack OneBitEncryption.scheme (TableMAC.scheme width) n) :
    (goal OneBitEncryption.scheme (TableMAC.scheme width)).advantage n () attack ≤ tagGuessBound width n := by
  have h := advantage_le OneBitEncryption.scheme (TableMAC.scheme width) n attack
  rw [OneBitEncryption.advantage_zero, zero_add] at h
  exact h.trans (TableMAC.reduction_advantage_le width n attack.2)

theorem encryption_bound (width : Nat → Nat) :
    BoundedByOnWithin (encryptionGoal OneBitEncryption.scheme)
      (encryptionBackend width).adversaries (fun _ => ()) (fun _ => 0) := by
  intro attacks _ n
  exact le_of_eq (OneBitEncryption.advantage_zero n (attacks n))

/-- Signing-query certificates are explicit in the base assumption class. -/
def oneQueryClass (width : Nat → Nat) :
    AdversaryClass (macGoal OneBitEncryption.scheme (TableMAC.scheme width)) where
  admissible := fun _ attacks => ∀ n, ∀ attack ∈ (attacks n).support, attack.BoundedQueries 1

theorem mac_bound (width : Nat → Nat) :
    BoundedByOnWithin (macGoal OneBitEncryption.scheme (TableMAC.scheme width))
      (oneQueryClass width) (fun _ => ()) (tagGuessBound width) := by
  intro attacks hAttacks n
  exact TableMAC.mac_advantage_le width n (attacks n) (hAttacks n)

/-- Substitute 0 and the tag-guess bound into the translated semantic rule.
The concrete encryption witness supplies its first premise's admissibility;
the one-use state supplies the second premise's signing-query certificate. -/
theorem source_bound (width : Nat → Nat) :
    BoundedByOnWithin (goal OneBitEncryption.scheme (TableMAC.scheme width))
      (sourceBackend width).adversaries (fun _ => ()) (tagGuessBound width) := by
  have h := Logic.bounded OneBitEncryption.scheme (TableMAC.scheme width)
    (encryptionBackend width).adversaries (oneQueryClass width)
    (fun _ => 0) (tagGuessBound width) (encryption_bound width) (mac_bound width)
  simp only [zero_add] at h
  intro attacks hAttacks n
  apply h attacks ?_ n
  constructor
  · exact (realization width).certificate.left.admissible _ attacks hAttacks
  · intro index program hProgram
    change program ∈ (integrityReduction OneBitEncryption.scheme (TableMAC.scheme width)
      index (attacks index).2).support at hProgram
    rw [integrityReduction, PMF.mem_support_map_iff] at hProgram
    obtain ⟨key, _, he⟩ := hProgram
    subst program
    exact TableMAC.reduction_queries width index key (attacks index).2

/-- The actual native privacy experiments have identical outcome laws. -/
theorem native_privacy_zero (width : Nat → Nat) (n : Nat) (code : Interactive.Code)
    (count : Nat) (input : List Bool)
    (hStops : ∀ side key, key ∈ (OneBitEncryption.scheme.keygen n).support →
      NativePrivacyGame.SourceStops width n key side code count input) :
    NativePrivacyGame.advantage width n code count input = 0 := by
  rw [NativePrivacyGame.advantage_eq width n code count input hStops]
  exact OneBitEncryption.advantage_zero n _

/-- The actual native MAC experiment uses its real signing history. -/
theorem native_forgery_bound (width : Nat → Nat) (n : Nat) (code : Interactive.Code)
    (count : Nat) (input : List Bool)
    (hStops : ∀ macKey ∈ ((TableMAC.scheme width).keygen n).support,
      IntegrityGameObservation.SourceStops width n macKey code count input) :
    NativeIntegrityGame.advantage width n code count input ≤ tagGuessBound width n := by
  rw [NativeIntegrityGame.advantage_eq width n code count input hStops]
  exact TableMAC.reduction_advantage_le width n _

/-- One source witness provides unconditional probability bounds, exact finite
outputs, genuine native stopping/game certificates, and explicit CPU budgets. -/
theorem witness_security (width : Nat → Nat)
    (A : AdversaryFamily (goal OneBitEncryption.scheme (TableMAC.scheme width)) (fun _ => ()))
    (W : (sourceBackend width).object.Witness (fun _ => ()) A) (n : Nat) :
    (goal OneBitEncryption.scheme (TableMAC.scheme width)).advantage n () (A n) ≤ tagGuessBound width n ∧
    PrivacyBackend.TargetExecutes width (encryptionCompiler.run W.code)
      ((realization width).encryptionWitness _ _ W).resources ∧
    IntegrityBackend.TargetExecutes width (macCompiler.run W.code)
      ((realization width).macWitness _ _ W).resources := by
  exact ⟨source_bound width A W.admissible n,
    ((realization width).compiled_executes A W).1,
    ((realization width).compiled_executes A W).2⟩

end Foundation.Symmetric.EncryptThenMAC.ConcreteSecurity
