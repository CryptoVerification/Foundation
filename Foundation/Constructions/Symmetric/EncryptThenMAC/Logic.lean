import Foundation.Constructions.Symmetric.EncryptThenMAC.Security
import Foundation.Logic.Translation

/-! A high-level two-assumption authenticated-encryption rule expands to
separate privacy and integrity reductions followed by their combination.
Bounds are symbolic expressions; the derivation contains no schemes, keys,
probability measures, or security assumptions. -/
namespace Foundation.Symmetric.EncryptThenMAC.Logic

open scoped ENNReal
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Bound where
  | encryption | mac
  | add : Bound → Bound → Bound

inductive Object where
  | encryption | mac | privacy | integrity | authenticated

structure Claim where
  object : Object
  bound : Bound

inductive Rule where
  | privacy (bound : Bound)
  | integrity (bound : Bound)
  | combine (privacy integrity : Bound)

abbrev lower : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .privacy _ | .integrity _ => 1 | .combine _ _ => 2
  premise := fun
    | .privacy ε => fun _ => ⟨.encryption, ε⟩
    | .integrity ε => fun _ => ⟨.mac, ε⟩
    | .combine ε δ => Fin.cases ⟨.privacy, ε⟩ (fun _ => ⟨.integrity, δ⟩)
  conclusion := fun
    | .privacy ε => ⟨.privacy, ε⟩
    | .integrity ε => ⟨.integrity, ε⟩
    | .combine ε δ => ⟨.authenticated, .add ε δ⟩

abbrev higher : Presentation where
  Judgment := Claim
  Rule := Bound × Bound
  arity := fun _ => 2
  premise := fun (ε, δ) => Fin.cases ⟨.encryption, ε⟩ (fun _ => ⟨.mac, δ⟩)
  conclusion := fun (ε, δ) => ⟨.authenticated, .add ε δ⟩

abbrev expansion : Translation higher lower where
  judgment := id
  rule := fun (ε, δ) =>
    Derivation.apply (T := lower) (.combine ε δ) (Fin.cases
      (Derivation.apply (T := lower) (.privacy ε)
        (fun _ => Derivation.hypothesis (T := lower)
          (Γ := (higher.ruleContext (ε, δ)).map id) 0))
      (fun _ => Derivation.apply (T := lower) (.integrity δ)
        (fun _ => Derivation.hypothesis (T := lower)
          (Γ := (higher.ruleContext (ε, δ)).map id) 1)))

abbrev context : Context higher where
  length := 2
  claim := Fin.cases ⟨.encryption, .encryption⟩ (fun _ => ⟨.mac, .mac⟩)

def proof : Derivation higher context ⟨.authenticated, .add .encryption .mac⟩ :=
  Derivation.apply (T := higher) (.encryption, .mac)
    (fun i => Derivation.hypothesis (T := higher) (Γ := context) i)

def Bound.eval (ε δ : Nat → ℝ≥0∞) : Bound → Nat → ℝ≥0∞
  | .encryption => ε
  | .mac => δ
  | .add a b => fun n => a.eval ε δ n + b.eval ε δ n

noncomputable def model (E : Encryption) (M : MAC E.Ciphertext)
    (CE : AdversaryClass (encryptionGoal E)) (CM : AdversaryClass (macGoal E M))
    (ε δ : Nat → ℝ≥0∞) : Model lower where
  Carrier := fun claim => match claim.object with
    | .encryption => BoundedByOnWithin (encryptionGoal E) CE (fun _ => ()) (claim.bound.eval ε δ)
    | .mac => BoundedByOnWithin (macGoal E M) CM (fun _ => ()) (claim.bound.eval ε δ)
    | .privacy => PrivacyBound E M CE CM (claim.bound.eval ε δ)
    | .integrity => IntegrityBound E M CE CM (claim.bound.eval ε δ)
    | .authenticated => BoundedByOnWithin (goal E M) (sourceClass E M CE CM)
        (fun _ => ()) (claim.bound.eval ε δ)
  operation := fun rule children => match rule with
    | .privacy bound => privacy_bounded E M CE CM (bound.eval ε δ) (children 0)
    | .integrity bound => integrity_bounded E M CE CM (bound.eval ε δ) (children 0)
    | .combine a b => combine_bounded E M CE CM (a.eval ε δ) (b.eval ε δ) (children 0) (children 1)

/-- The actual two-assumption theorem is obtained by translating one fixed
high-level proof and interpreting its three lower-level inference steps. -/
theorem bounded (E : Encryption) (M : MAC E.Ciphertext)
    (CE : AdversaryClass (encryptionGoal E)) (CM : AdversaryClass (macGoal E M))
    (ε δ : Nat → ℝ≥0∞)
    (hE : BoundedByOnWithin (encryptionGoal E) CE (fun _ => ()) ε)
    (hM : BoundedByOnWithin (macGoal E M) CM (fun _ => ()) δ) :
    BoundedByOnWithin (goal E M) (sourceClass E M CE CM) (fun _ => ()) (fun n => ε n + δ n) := by
  exact (expansion.translate proof).eval (Γ := context.map (U := lower) id) (model E M CE CM ε δ)
    (fun i => by fin_cases i; exact hE; exact hM)

end Foundation.Symmetric.EncryptThenMAC.Logic
