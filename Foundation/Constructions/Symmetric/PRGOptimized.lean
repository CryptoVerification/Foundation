import Foundation.Constructions.Symmetric.PRGResource
import Foundation.Crypto.Semantics.Machine.MaskingAdministrative
import Foundation.Crypto.Logic.General.ResourceImprovement

/-! A real implementation improvement of both PRG encryption reductions.
The tagged finite code selects the original or fused masking controller.
All native attack instructions and randomness remain unchanged. Execution
uses the same cell-level transition accounting, with one phase dispatch
removed. Quantitative security retains the original two-branch loss. -/
namespace Foundation.Symmetric.Generator.Optimized
open Foundation.Probability Machine CryptoLogic.General
open CryptoLogic.General.ResourceImprovement
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Mode where
  | original | fused
  deriving DecidableEq, Repr, Encodable

/-- The Boolean distinguishes native inputs from challenge-controller code. -/
def Code : Bool → Type
  | false => Machine.Program
  | true => Mode × Masking.Code

inductive Primitive : Bool → Bool → Type where
  | mask (mode : Mode) (side : Bool) : Primitive false true
  | appendHalt : Primitive true true

def Primitive.encode {m n} : Primitive m n → Option (Mode × Bool)
  | .mask mode side => some (mode, side)
  | .appendHalt => none

def Primitive.decode (m n : Bool) (code : Option (Mode × Bool)) : Option (Primitive m n) :=
  match m, n, code with
  | false, true, some (mode, side) => some (.mask mode side)
  | true, true, none => some .appendHalt
  | _, _, _ => none

instance (m n : Bool) : Encodable (Primitive m n) :=
  Encodable.ofLeftInjection Primitive.encode (Primitive.decode m n) (by intro p; cases p <;> rfl)

def system : CodeSystem where
  Machine := Bool
  Code := Code
  machineEncodable := inferInstance
  Primitive := Primitive
  codeEncodable := fun b => by cases b <;> dsimp [Code] <;> infer_instance
  primitiveEncodable := fun _ _ => inferInstance
  runPrimitive := fun primitive program => match primitive with
    | .mask mode side => (mode, Masking.compile side program)
    | .appendHalt => (program.1, Masking.appendHalt program.2)

noncomputable def eval (code : Mode × Masking.Code) (start : Masking.Configuration) (time : Nat) :=
  match code.1 with
  | .original => Masking.eval code.2 start time
  | .fused => Masking.Fused.eval code.2 start time

def time (G : Generator) (nativeTime : Nat → Nat) (n : Nat) : Nat :=
  2 * n + 10 * G.outputLength n + 8 + nativeTime n

theorem time_saving (G : Generator) (nativeTime : Nat → Nat) (n : Nat) :
    time G nativeTime n + 1 = G.reductionTime nativeTime n := by
  unfold time reductionTime
  omega

theorem time_strict (G : Generator) (nativeTime : Nat → Nat) (n : Nat) :
    time G nativeTime n < G.reductionTime nativeTime n := by
  rw [← time_saving]
  omega

theorem time_polynomial (G : Generator) {nativeTime : Nat → Nat}
    (ht : PolynomiallyBounded nativeTime) (hL : PolynomiallyBounded G.outputLength) :
    PolynomiallyBounded (time G nativeTime) :=
  PolynomiallyBounded.mono (fun n => Nat.le_of_lt (time_strict G nativeTime n))
    (G.reductionTime_polynomial ht hL)

/-- Equality of the whole retained-configuration distribution, not just its
last bit. Both start at the same physical input and run the same native code. -/
theorem eval_saved (G : Generator) (nativeTime : Nat → Nat) (side : Bool)
    (program : Machine.Program) (n : Nat) (I : G.Messages n)
    (challenge : Bits (G.outputLength n)) :
    Masking.Fused.eval (Masking.compile side program)
      (Masking.initial (Masking.compile side program) (G.header n I)
        I.1.toList I.2.toList challenge.toList) (time G nativeTime n) =
    Masking.eval (Masking.compile side program)
      (Masking.initial (Masking.compile side program) (G.header n I)
        I.1.toList I.2.toList challenge.toList) (G.reductionTime nativeTime n) := by
  have fusedOverhead : Masking.Fused.overhead (G.header n I).length challenge.toList.length =
      2 * n + 10 * G.outputLength n + 8 := by
    rw [G.header_length, Bits.length_toList]
    unfold Masking.Fused.overhead
    omega
  have oldOverhead : Masking.overhead (G.header n I).length challenge.toList.length =
      2 * n + 10 * G.outputLength n + 9 := by
    rw [Bits.length_toList, G.overhead_eq]
  unfold time reductionTime
  rw [← fusedOverhead, ← oldOverhead]
  simp only [Masking.compile]
  have hNonempty : 0 < (G.header n I).length + challenge.toList.length := by
    rw [G.header_length, Bits.length_toList]
    omega
  rw [Masking.Fused.masked_eval side program (G.header n I) I.1.toList I.2.toList
      challenge.toList hNonempty (by simp) (by simp),
    Masking.masked_eval side program (G.header n I) I.1.toList I.2.toList challenge.toList
      (by simp) (by simp)]
  change Masking.Fused.eval _ (.running _) _ = Masking.eval _ (.running _) _
  rw [Masking.Fused.running_eval, Masking.running_eval]

noncomputable section

/-- The source class and all native stopping/realization obligations are the
existing PRG encryption class, with the same source program. -/
def source (G : Generator) (nativeTime : Nat → Nat) : SecurityObject.{0, 0} system false where
  goal := G.encryptionGoal
  execution := {
    Resources := Unit
    ExecutesWithin := fun F program _ => ∀ n (challenge : Bits (G.outputLength n)),
      Masking.HaltsWithin (.native program) (Masking.initial (.native program) (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList) (nativeTime n)
    Realizes := fun F A program _ => ∀ n challenge,
      Masking.output (.native program) (Masking.initial (.native program) (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList) (nativeTime n) = (A n challenge).map some }
  adversaries := G.nativeClass nativeTime
  represented := by
    intro F A ⟨W⟩
    exact ⟨W.program, (), W.halts, W.realizes⟩

def executes (G : Generator) (F : InstanceFamily G.prgGoal) (code : Mode × Masking.Code)
    (budget : Nat → Nat) : Prop :=
  PolynomiallyBounded budget ∧ ∀ n (challenge : Bits (G.outputLength n)),
    ∀ finish ∈ (eval code (Masking.initial code.2 (G.header n (F n))
      (F n).1.toList (F n).2.toList challenge.toList) (budget n)).support, Masking.complete finish

def realizes (G : Generator) (F : InstanceFamily G.prgGoal) (A : AdversaryFamily G.prgGoal F)
    (code : Mode × Masking.Code) (budget : Nat → Nat) : Prop :=
  ∀ n (challenge : Bits (G.outputLength n)),
    (eval code (Masking.initial code.2 (G.header n (F n))
      (F n).1.toList (F n).2.toList challenge.toList) (budget n)).map Masking.result =
        (A n challenge).map some

/-- A single target backend evaluates both tagged implementations. Its
resources are the original natural-valued transition-budget profiles. -/
def target (G : Generator) : SecurityObject.{0, 0} system true where
  goal := G.prgGoal
  execution := { Resources := Nat → Nat, ExecutesWithin := executes G, Realizes := realizes G }
  adversaries := ⟨fun F A => ∃ code budget, executes G F code budget ∧ realizes G F A code budget⟩
  represented := by intro F A h; exact h

instance (G : Generator) : PartialOrder (target G).execution.Resources :=
  inferInstanceAs (PartialOrder (Nat → Nat))

def semantic (G : Generator) (side : Bool) : CryptoLogic.AdversaryTransform G.encryptionGoal G.prgGoal :=
  ⟨fun I => I, fun I A => G.reduce I side A⟩

def originalNative (G : Generator) (nativeTime : Nat → Nat) (F A)
    (W : (source G nativeTime).Witness F A) : G.NativeWitness nativeTime F A :=
  ⟨W.code, W.executes, W.realizes⟩

def budget (G : Generator) (nativeTime : Nat → Nat) : Mode → Nat → Nat
  | .original => G.reductionTime nativeTime
  | .fused => time G nativeTime

def witness (G : Generator) (nativeTime : Nat → Nat)
    (ht : PolynomiallyBounded nativeTime) (hL : PolynomiallyBounded G.outputLength)
    (mode : Mode) (side : Bool) (F A) (W : (source G nativeTime).Witness F A) :
    (target G).Witness ((semantic G side).mapFamily F) ((semantic G side).mapAdversaryFamily F A) := by
  let old := G.mapWitness nativeTime side F A (originalNative G nativeTime F A W)
  let code : Mode × Masking.Code := (mode, Masking.compile side W.code)
  let b := budget G nativeTime mode
  have hExec : executes G F code b := by
    constructor
    · cases mode with
      | original => exact G.reductionTime_polynomial ht hL
      | fused => exact time_polynomial G ht hL
    · intro n challenge finish hf
      cases mode with
      | original => exact old.halts n challenge finish hf
      | fused =>
          change finish ∈ (Masking.Fused.eval _ _ (time G nativeTime n)).support at hf
          rw [eval_saved] at hf
          exact old.halts n challenge finish hf
  have hReal : realizes G F (fun n => G.reduce (F n) side (A n)) code b := by
    intro n challenge
    cases mode with
    | original => exact old.realizes n challenge
    | fused =>
        change (Masking.Fused.eval _ _ (time G nativeTime n)).map _ = _
        rw [eval_saved]
        exact old.realizes n challenge
  exact ⟨code, b, hExec, hReal, ⟨code, b, hExec, hReal⟩⟩

def implementation (G : Generator) (nativeTime : Nat → Nat)
    (ht : PolynomiallyBounded nativeTime) (hL : PolynomiallyBounded G.outputLength)
    (mode : Mode) (side : Bool) :
    Implementation (source G nativeTime) (target G) (semantic G side) where
  compiler := .primitive (.mask mode side)
  mapWitness := witness G nativeTime ht hL mode side
  code_eq := by intros; rfl

theorem improves (G : Generator) (nativeTime : Nat → Nat)
    (ht : PolynomiallyBounded nativeTime) (hL : PolynomiallyBounded G.outputLength) (side : Bool) :
    Implementation.Improves (implementation G nativeTime ht hL .fused side)
      (implementation G nativeTime ht hL .original side) := by
  intro F A W n
  exact Nat.le_of_lt (time_strict G nativeTime n)

theorem resources_strict (G : Generator) (nativeTime : Nat → Nat)
    (ht : PolynomiallyBounded nativeTime) (hL : PolynomiallyBounded G.outputLength) (side : Bool)
    (F A) (W : (source G nativeTime).Witness F A) (n : Nat) :
    ((implementation G nativeTime ht hL .fused side).mapWitness F A W).resources n <
      ((implementation G nativeTime ht hL .original side).mapWitness F A W).resources n :=
  time_strict G nativeTime n

theorem code_changed (G : Generator) (nativeTime : Nat → Nat)
    (ht : PolynomiallyBounded nativeTime) (hL : PolynomiallyBounded G.outputLength) (side : Bool)
    (F A) (W : (source G nativeTime).Witness F A) :
    ((implementation G nativeTime ht hL .fused side).mapWitness F A W).code ≠
      ((implementation G nativeTime ht hL .original side).mapWitness F A W).code := by
  intro h
  have impossible := congrArg Prod.fst h
  cases impossible

/-- A one-transition tighter target budget suffices for both branches. -/
def tight (G : Generator) (nativeTime : Nat → Nat)
    (ht : PolynomiallyBounded nativeTime) (hL : PolynomiallyBounded G.outputLength) (side : Bool) :=
  (implementation G nativeTime ht hL .fused side).constrain
    (fun r => ∀ n, r n ≤ time G nativeTime n) (by intros; exact le_rfl)

def binary (G : Generator) (nativeTime : Nat → Nat)
    (ht : PolynomiallyBounded nativeTime) (hL : PolynomiallyBounded G.outputLength) :
    CertifiedBinaryReduction (source G nativeTime)
      ((target G).refine (fun _ _ r => ∀ n, r n ≤ time G nativeTime n))
      ((target G).refine (fun _ _ r => ∀ n, r n ≤ time G nativeTime n)) where
  left := (tight G nativeTime ht hL false).certified
  right := (tight G nativeTime ht hL true).certified
  leftLoss := AdvantageBound.id
  rightLoss := AdvantageBound.id
  leftNegligible := AdvantageBound.id_preservesNegligible
  rightNegligible := AdvantageBound.id_preservesNegligible
  advantage_le := by
    intro F A n
    exact G.advantage_le n (F n) (A n)

theorem bounded (G : Generator) (nativeTime : Nat → Nat)
    (ht : PolynomiallyBounded nativeTime) (hL : PolynomiallyBounded G.outputLength)
    (F : InstanceFamily G.encryptionGoal) (ε : Nat → ℝ≥0∞)
    (h : ((target G).refine (fun _ _ r => ∀ n, r n ≤ time G nativeTime n)).Bounded F ε) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass nativeTime) F (fun n => 2 * ε n) := by
  have bound := (binary G nativeTime ht hL).bounded F ε ε h h
  change BoundedByOnWithin G.encryptionGoal (G.nativeClass nativeTime) F
    (fun n => ε n + ε n) at bound
  simpa only [two_mul] using bound

end
end Foundation.Symmetric.Generator.Optimized
