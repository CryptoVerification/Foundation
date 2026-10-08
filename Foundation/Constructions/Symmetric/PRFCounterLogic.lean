import Foundation.Constructions.Symmetric.PRFCounterResource
import Foundation.Crypto.Meta.General.ResourceSecurity

/-! The resource-certified multi-encryption theorem uses the existing binary
inference rule. Both leaves use one PRF assumption, but retain distinct
finite compiled code and separate advantage terms. -/
namespace Foundation.Symmetric.PRFCounter.Logic
open CryptoLogic.General Resource
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Object where
  | encryption | prf
  deriving DecidableEq, Repr

def machine : Object → Kind
  | .encryption => .source
  | .prf => .target

inductive Binary : Object → Object → Object → Type where
  | encryption : Binary .encryption .prf .prf

abbrev language : Language system where
  Object := Object
  machine := machine
  Unary := fun _ _ => PEmpty
  unaryCompiler := fun p => nomatch p
  Binary := Binary
  binaryCompilers := fun p => match p with
    | .encryption => (.primitive (.wrap false), .primitive (.wrap true))

noncomputable def certificate (S : Scheme) (time q : Nat → Nat) :
    CertifiedBinaryReduction (sourceObject S time q)
      (targetObject S (reductionTime S time) q) (targetObject S (reductionTime S time) q) where
  left := transform S time q false
  right := transform S time q true
  leftLoss := AdvantageBound.id
  rightLoss := AdvantageBound.id
  leftNegligible := AdvantageBound.id_preservesNegligible
  rightNegligible := AdvantageBound.id_preservesNegligible
  advantage_le := by intro F A n; exact advantage_le_prf S n (A n)

noncomputable def signature (S : Scheme) (time q : Nat → Nat) : Signature language where
  interpret := fun X => match X with
    | .encryption => sourceObject S time q
    | .prf => targetObject S (reductionTime S time) q
  unary := fun p => nomatch p
  unary_compiler := fun p => nomatch p
  binary := fun p => match p with | .encryption => certificate S time q
  left_compiler := by intro X Y Z p; cases p; rfl
  right_compiler := by intro X Y Z p; cases p; rfl

@[macro_inline] def context (S : Scheme) (time q : Nat → Nat) : Context (signature S time q) where
  length := 2
  claim _ := ⟨Object.prf, fun _ => ()⟩

@[macro_inline] def derivation (S : Scheme) (time q : Nat → Nat) :
    Derivation (signature S time q) (context S time q) Object.encryption (fun _ => ()) :=
  Derivation.binary (S := signature S time q) (Γ := context S time q) Binary.encryption (fun _ => ())
    (Derivation.hypothesis (S := signature S time q) (Γ := context S time q) ⟨0, by change 0 < 2; decide⟩)
    (Derivation.hypothesis (S := signature S time q) (Γ := context S time q) ⟨1, by change 1 < 2; decide⟩)

noncomputable def tree (S : Scheme) (time q : Nat → Nat) :
    Tree (signature S time q) (context S time q) Object.encryption (fun _ => ()) :=
  Tree.binary (S := signature S time q) (Γ := context S time q) Binary.encryption (fun _ => ())
    (Tree.hypothesis (S := signature S time q) (Γ := context S time q) ⟨0, by change 0 < 2; decide⟩)
    (Tree.hypothesis (S := signature S time q) (Γ := context S time q) ⟨1, by change 1 < 2; decide⟩)

noncomputable def analysis (S : Scheme) (time q : Nat → Nat) :
    Derivation.Analysis (derivation S time q) := ⟨tree S time q, rfl⟩

@[macro_inline] def sharedContext (S : Scheme) (time q : Nat → Nat) : Context (signature S time q) where
  length := 1
  claim _ := ⟨Object.prf, fun _ => ()⟩

@[macro_inline] def sharedDerivation (S : Scheme) (time q : Nat → Nat) :
    Derivation (signature S time q) (sharedContext S time q) Object.encryption (fun _ => ()) :=
  (derivation S time q).substitute (fun _ =>
    Derivation.hypothesis (S := signature S time q) (Γ := sharedContext S time q)
      ⟨0, by change 0 < 1; decide⟩)

noncomputable def sharedAnalysis (S : Scheme) (time q : Nat → Nat) :
    Derivation.Analysis (sharedDerivation S time q) :=
  (analysis S time q).substitute
    (fun _ => Derivation.hypothesis (S := signature S time q) (Γ := sharedContext S time q)
      ⟨0, by change 0 < 1; decide⟩)
    (fun _ => ⟨Tree.hypothesis (S := signature S time q) (Γ := sharedContext S time q)
      ⟨0, by change 0 < 1; decide⟩, rfl⟩)

theorem run (S : Scheme) (time q : Nat → Nat) (code : CryptoOracle.Interactive.Code) :
    (sharedDerivation S time q).run code =
      [(0, ⟨Kind.target, CryptoOracle.CounterMasking.compile false code⟩),
       (0, ⟨Kind.target, CryptoOracle.CounterMasking.compile true code⟩)] := rfl

theorem loss (S : Scheme) (time q : Nat → Nat) (ε : Fin 1 → Nat → ℝ≥0∞) (n : Nat) :
    (sharedAnalysis S time q).loss.eval ε n = 2 * ε 0 n := by
  change ε 0 n + ε 0 n = 2 * ε 0 n
  rw [two_mul]

/-- General soundness transports resource-restricted PRF security. -/
theorem secure (S : Scheme) (time q : Nat → Nat)
    (h : (targetObject S (reductionTime S time) q).Secure (fun _ => ())) :
    (sourceObject S time q).Secure (fun _ => ()) := by
  apply (sharedDerivation S time q).sound
  intro i
  exact h

/-- The two premise occurrences may carry different concrete bounds. -/
theorem bounded_sum (S : Scheme) (time q : Nat → Nat) (ε₀ ε₁ : Nat → ℝ≥0∞)
    (h₀ : (targetObject S (reductionTime S time) q).Bounded (fun _ => ()) ε₀)
    (h₁ : (targetObject S (reductionTime S time) q).Bounded (fun _ => ()) ε₁) :
    (sourceObject S time q).Bounded (fun _ => ()) (fun n => ε₀ n + ε₁ n) := by
  exact (certificate S time q).bounded (fun _ => ()) ε₀ ε₁ h₀ h₁

/-- General loss analysis gives the concrete resource-restricted bound. -/
theorem bounded (S : Scheme) (time q : Nat → Nat) (ε : Nat → ℝ≥0∞)
    (h : (targetObject S (reductionTime S time) q).Bounded (fun _ => ()) ε) :
    (sourceObject S time q).Bounded (fun _ => ()) (fun n => 2 * ε n) := by
  intro A hA n
  have hb := (sharedAnalysis S time q).bounded (fun _ => ε) (fun _ => h) A hA n
  change advantageProfile (sourceObject S time q).goal (fun _ => ()) A n ≤
    (sharedAnalysis S time q).loss.eval (fun _ => ε) n at hb
  rw [loss] at hb
  exact hb

end Foundation.Symmetric.PRFCounter.Logic
