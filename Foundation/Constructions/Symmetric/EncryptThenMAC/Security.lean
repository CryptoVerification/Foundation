import Foundation.Constructions.Symmetric.EncryptThenMAC.Integrity

/-! Two-assumption semantic security for stateful encrypt-then-MAC. The source
advantage is the maximum of chosen-plaintext distinguishing advantage and
ciphertext-forgery probability. The keys are sampled independently, and the
MAC notion is strong unforgeability of ciphertext/tag pairs. This module does
not assert chosen-ciphertext privacy or CPU bounds for host-language code. -/
namespace Foundation.Symmetric.EncryptThenMAC

open Foundation.Probability CryptoOracle
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable (E : Encryption) (M : MAC E.Ciphertext)

noncomputable def encryptionGame (n : Nat) (side : Bool)
    (attack : ProbComp (EncryptionAttack E n)) : ProbComp Bool :=
  (E.keygen n).bind fun key => attack.bind fun program =>
    (program.run (encryptionOracle E n key side) (E.initial n)).map Outcome.result

noncomputable def privacyGame (n : Nat) (side : Bool) (attack : PrivacyAttack E M n) : ProbComp Bool :=
  (E.keygen n).bind fun key => (M.keygen n).bind fun macKey =>
    (attack.run (privacyOracle E M n key macKey side) (E.initial n)).map Outcome.result

noncomputable def privacyReduction (n : Nat) (attack : PrivacyAttack E M n) :
    ProbComp (EncryptionAttack E n) := (M.keygen n).map fun macKey => reducePrivacy E M macKey attack

theorem privacyGame_eq (n : Nat) (side : Bool) (attack : PrivacyAttack E M n) :
    privacyGame E M n side attack = encryptionGame E n side (privacyReduction E M n attack) := by
  simp only [privacyGame, encryptionGame, privacyReduction, PMF.bind_map]
  congr 1
  funext key
  congr 1
  funext macKey
  exact (privacy_simulation E M key macKey side (E.initial n) attack).symm

abbrev IntegrityRecord (n : Nat) := E.Key n × M.Key n ×
  (AuthCiphertext E M n × List (AuthCiphertext E M n))
abbrev MACRecord (n : Nat) := M.Key n ×
  (AuthCiphertext E M n × List (AuthCiphertext E M n))

noncomputable def integrityGame (n : Nat) (attack : IntegrityAttack E M n) :
    ProbComp (IntegrityRecord E M n) :=
  (E.keygen n).bind fun key => (M.keygen n).bind fun macKey =>
    (attack.run (integrityOracle E M n key macKey) (E.initial n)).map
      (fun out => (key, macKey, integrityRecord E M out))

-- Private adversary coins may be sampled before the independent MAC key.
noncomputable def macGame (n : Nat) (attack : ProbComp (MACAttack E M n)) :
    ProbComp (MACRecord E M n) :=
  attack.bind fun program => (M.keygen n).bind fun macKey =>
    (program.run (signingOracle E M n macKey) ()).map
      (fun out => (macKey, signingRecord E M out))

noncomputable def integrityReduction (n : Nat) (attack : IntegrityAttack E M n) :
    ProbComp (MACAttack E M n) :=
  (E.keygen n).map fun key => reduceIntegrity E M key (E.initial n) attack

/-- Forgetting only the private encryption key leaves precisely the MAC
forgery experiment, including the complete signing transcript. -/
theorem integrityGame_project (n : Nat) (attack : IntegrityAttack E M n) :
    (integrityGame E M n attack).map Prod.snd = macGame E M n (integrityReduction E M n attack) := by
  simp only [integrityGame, macGame, integrityReduction, PMF.bind_map, PMF.map_bind,
    PMF.map_comp, Function.comp_def]
  congr 1
  funext key
  congr 1
  funext macKey
  have hi := congrArg (fun p => p.map (fun record => (macKey, record)))
    (integrity_simulation E M key macKey (E.initial n) attack)
  simpa only [PMF.map_comp, Function.comp_def] using hi.symm

noncomputable def integrityAdvantage (n : Nat) (attack : IntegrityAttack E M n) : ℝ≥0∞ :=
  eventProb (integrityGame E M n attack) (fun record => integrityWins E M record.1 record.2.1 record.2.2)

noncomputable def macAdvantage (n : Nat) (attack : ProbComp (MACAttack E M n)) : ℝ≥0∞ :=
  eventProb (macGame E M n attack) (fun record => macWins E M record.1 record.2)

theorem integrity_advantage_le (n : Nat) (attack : IntegrityAttack E M n) :
    integrityAdvantage E M n attack ≤ macAdvantage E M n (integrityReduction E M n attack) := by
  rw [macAdvantage, ← integrityGame_project]
  unfold integrityAdvantage eventProb
  rw [PMF.toOuterMeasure_map_apply]
  apply MeasureTheory.OuterMeasure.mono
  intro record h
  exact integrityWins_implies_macWins E M record.1 record.2.1 record.2.2 h

noncomputable def encryptionGoal : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun n _ => ProbComp (EncryptionAttack E n)
  advantage := fun n _ attack => probabilityGap
    (eventProb (encryptionGame E n false attack) (· = true))
    (eventProb (encryptionGame E n true attack) (· = true))

noncomputable def macGoal : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun n _ => ProbComp (MACAttack E M n)
  advantage := fun n _ attack => macAdvantage E M n attack

abbrev Attack (n : Nat) := PrivacyAttack E M n × IntegrityAttack E M n

noncomputable def goal : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun n _ => Attack E M n
  advantage := fun n _ attack => max
    (probabilityGap (eventProb (privacyGame E M n false attack.1) (· = true))
      (eventProb (privacyGame E M n true attack.1) (· = true)))
    (integrityAdvantage E M n attack.2)

/-- Both genuinely different assumptions occur in the quantitative bound. -/
theorem advantage_le (n : Nat) (attack : Attack E M n) :
    (goal E M).advantage n () attack ≤
      (encryptionGoal E).advantage n () (privacyReduction E M n attack.1) +
      (macGoal E M).advantage n () (integrityReduction E M n attack.2) := by
  change max _ _ ≤ _ + _
  apply max_le
  · rw [privacyGame_eq, privacyGame_eq]
    exact le_self_add
  · exact (integrity_advantage_le E M n attack.2).trans le_add_self

/-- Admissibility records both concrete reduction obligations. A CPU backend
must prove these obligations from its own source execution certificate. -/
def sourceClass (CE : AdversaryClass (encryptionGoal E)) (CM : AdversaryClass (macGoal E M)) :
    AdversaryClass (goal E M) where
  admissible _ A :=
    CE.admissible (fun _ => ()) (fun n => privacyReduction E M n (A n).1) ∧
    CM.admissible (fun _ => ()) (fun n => integrityReduction E M n (A n).2)

def PrivacyBound (CE : AdversaryClass (encryptionGoal E)) (CM : AdversaryClass (macGoal E M))
    (ε : Nat → ℝ≥0∞) : Prop :=
  ∀ A : AdversaryFamily (goal E M) (fun _ => ()),
    (sourceClass E M CE CM).admissible (fun _ => ()) A → ∀ n,
      probabilityGap (eventProb (privacyGame E M n false (A n).1) (· = true))
        (eventProb (privacyGame E M n true (A n).1) (· = true)) ≤ ε n

def IntegrityBound (CE : AdversaryClass (encryptionGoal E)) (CM : AdversaryClass (macGoal E M))
    (ε : Nat → ℝ≥0∞) : Prop :=
  ∀ A : AdversaryFamily (goal E M) (fun _ => ()),
    (sourceClass E M CE CM).admissible (fun _ => ()) A → ∀ n,
      integrityAdvantage E M n (A n).2 ≤ ε n

theorem privacy_bounded (CE : AdversaryClass (encryptionGoal E))
    (CM : AdversaryClass (macGoal E M)) (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin (encryptionGoal E) CE (fun _ => ()) ε) :
    PrivacyBound E M CE CM ε := by
  intro A hA n
  rw [privacyGame_eq, privacyGame_eq]
  exact h (fun n => privacyReduction E M n (A n).1) hA.1 n

theorem integrity_bounded (CE : AdversaryClass (encryptionGoal E))
    (CM : AdversaryClass (macGoal E M)) (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin (macGoal E M) CM (fun _ => ()) ε) :
    IntegrityBound E M CE CM ε := by
  intro A hA n
  exact (integrity_advantage_le E M n (A n).2).trans
    (h (fun n => integrityReduction E M n (A n).2) hA.2 n)

theorem combine_bounded (CE : AdversaryClass (encryptionGoal E))
    (CM : AdversaryClass (macGoal E M)) (ε δ : Nat → ℝ≥0∞)
    (hp : PrivacyBound E M CE CM ε) (hi : IntegrityBound E M CE CM δ) :
    BoundedByOnWithin (goal E M) (sourceClass E M CE CM) (fun _ => ()) (fun n => ε n + δ n) := by
  intro A hA n
  apply max_le
  · exact (hp A hA n).trans le_self_add
  · exact (hi A hA n).trans le_add_self

theorem secure (CE : AdversaryClass (encryptionGoal E))
    (CM : AdversaryClass (macGoal E M))
    (hE : SecureOnWithin (encryptionGoal E) CE (fun _ => ()))
    (hM : SecureOnWithin (macGoal E M) CM (fun _ => ())) :
    SecureOnWithin (goal E M) (sourceClass E M CE CM) (fun _ => ()) := by
  intro A hA
  exact Negligible.mono (fun n => advantage_le E M n (A n))
    ((hE (fun n => privacyReduction E M n (A n).1) hA.1).add
      (hM (fun n => integrityReduction E M n (A n).2) hA.2))

end Foundation.Symmetric.EncryptThenMAC
