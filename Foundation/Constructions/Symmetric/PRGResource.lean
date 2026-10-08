import Foundation.Constructions.Symmetric.PRGEncryption
import Foundation.Crypto.Semantics.Machine.Masking

/-! Uniform finite-code certificates for the one-time PRG encryption reduction.
The bound counts preprocessing and every native attack transition. The PRG
experiment supplies one challenge; generator evaluation is challenger work.
The public message pair is finite input, never an instance-family oracle. -/
namespace Foundation.Symmetric

open Foundation.Probability Machine CryptoLogic
open scoped ENNReal

namespace Bits

theorem toList_xor {length : Nat} (x y : Bits length) :
    (xor x y).toList = Masking.xorList x.toList y.toList := by
  induction length with
  | zero => simp [toList, List.ofFn_zero, Masking.xorList]
  | succ length ih =>
      simp only [toList, List.ofFn_succ, xor, Masking.xorList]
      exact congrArg (Bool.xor (x 0) (y 0) :: ·)
        (ih (fun i => x i.succ) (fun i => y i.succ))

end Bits

namespace Generator

set_option backward.isDefEq.respectTransparency false

def header (G : Generator) (n : Nat) (I : G.Messages n) : List Bool :=
  encodeSecurityParameter n ++ frame I.1.toList ++ frame I.2.toList

@[simp] theorem header_length (G : Generator) (n : Nat) (I : G.Messages n) :
    (G.header n I).length = n + 4 * G.outputLength n + 3 := by
  simp [header, encodeSecurityParameter, frame]
  omega

/-- Native attacks see the parameter, both public messages, and ciphertext.
Every input challenge and every native random branch must halt. -/
structure NativeWitness (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F) where
  program : Machine.Program
  halts : ∀ n (challenge : Bits (G.outputLength n)),
    Masking.HaltsWithin (.native program)
      (Masking.initial (.native program) (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList) (time n)
  realizes : ∀ n (challenge : Bits (G.outputLength n)),
    Masking.output (.native program)
      (Masking.initial (.native program) (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList) (time n) =
      (A n challenge).map some

/-- Targets may contain the finite XOR controller. Halting and realization
refer to its operational evaluator, not an uncharged host function. -/
structure ChallengeWitness (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.prgGoal) (A : AdversaryFamily G.prgGoal F) where
  code : Masking.Code
  halts : ∀ n (challenge : Bits (G.outputLength n)),
    Masking.HaltsWithin code
      (Masking.initial code (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList) (time n)
  realizes : ∀ n (challenge : Bits (G.outputLength n)),
    Masking.output code
      (Masking.initial code (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList) (time n) =
      (A n challenge).map some

def nativeClass (G : Generator) (time : Nat → Nat) : AdversaryClass G.encryptionGoal where
  admissible F A := Nonempty (G.NativeWitness time F A)

def challengeClass (G : Generator) (time : Nat → Nat) : AdversaryClass G.prgGoal where
  admissible F A := Nonempty (G.ChallengeWitness time F A)

/-- Public header copying, XOR, input loading and three control transitions.
The uniform overhead does not depend on attack code, message values, or coins. -/
def reductionTime (G : Generator) (time : Nat → Nat) (n : Nat) : Nat :=
  2 * n + 10 * G.outputLength n + 9 + time n

theorem overhead_eq (G : Generator) (n : Nat) (I : G.Messages n) :
    Masking.overhead (G.header n I).length (G.outputLength n) =
      2 * n + 10 * G.outputLength n + 9 := by
  rw [header_length]
  unfold Masking.overhead
  omega

/-- Exact finite code for both reduction branches. Only source code is an
argument: no security parameter, instance family, budget or proof is supplied. -/
def reductionPrograms (program : Machine.Program) : Masking.Code × Masking.Code :=
  (.masked false program, .masked true program)

/-- Construct the target certificate by the proved operational simulation. -/
def mapWitness (G : Generator) (time : Nat → Nat) (side : Bool)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A) :
    G.ChallengeWitness (G.reductionTime time) F (fun n => G.reduce (F n) side (A n)) where
  code := .masked side W.program
  halts := by
    intro n challenge finish hFinish
    have heval := Masking.masked_eval side W.program (G.header n (F n))
      (F n).1.toList (F n).2.toList challenge.toList
      (by simp) (by simp) (time n)
    rw [Bits.length_toList, G.overhead_eq] at heval
    have hMask : Masking.xorList (if side then (F n).2.toList else (F n).1.toList)
        challenge.toList = (Bits.xor (G.message (F n) side) challenge).toList := by
      rw [Bits.toList_xor]
      cases side <;> rfl
    rw [hMask] at heval
    change finish ∈ (Masking.eval _ _ (G.reductionTime time n)).support at hFinish
    unfold reductionTime at hFinish
    rw [heval] at hFinish
    exact W.halts n _ finish hFinish
  realizes := by
    intro n challenge
    have heval := Masking.masked_eval side W.program (G.header n (F n))
      (F n).1.toList (F n).2.toList challenge.toList
      (by simp) (by simp) (time n)
    rw [Bits.length_toList, G.overhead_eq] at heval
    have hMask : Masking.xorList (if side then (F n).2.toList else (F n).1.toList)
        challenge.toList = (Bits.xor (G.message (F n) side) challenge).toList := by
      rw [Bits.toList_xor]
      cases side <;> rfl
    rw [hMask] at heval
    unfold Masking.output reductionTime
    rw [heval]
    exact W.realizes n _

@[simp] theorem mapWitness_code (G : Generator) (time : Nat → Nat) (side : Bool)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A) :
    (G.mapWitness time side F A W).code = Masking.compile side W.program := rfl

/-- The emitted code itself halts on every challenge and every coin branch. -/
theorem emitted_halts (G : Generator) (time : Nat → Nat) (side : Bool)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A) (n : Nat) (challenge : Bits (G.outputLength n)) :
    Masking.HaltsWithin (Masking.compile side W.program)
      (Masking.initial (Masking.compile side W.program) (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList) (G.reductionTime time n) :=
  (G.mapWitness time side F A W).halts n challenge

/-- The full one-challenge experiment records exactly one PRG query, on
all supported native executions, not just on one deterministic test path. -/
theorem emitted_queries (G : Generator) (time : Nat → Nat) (side : Bool)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A) (n : Nat)
    (distribution : ProbComp (Bits (G.outputLength n)))
    (outcome : ChallengeOutcome (G.outputLength n) (Option Bool))
    (h : outcome ∈ (runChallenge distribution (fun challenge =>
      Masking.output (Masking.compile side W.program)
        (Masking.initial (Masking.compile side W.program) (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) (G.reductionTime time n))).support) :
    outcome.trace.length = 1 := runChallenge_queries _ _ outcome h

/-- The emitted native experiment's result and challenge trace realize the
semantic reduction, for either challenge distribution (or any other one). -/
theorem emitted_realizes (G : Generator) (time : Nat → Nat) (side : Bool)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A) (n : Nat)
    (distribution : ProbComp (Bits (G.outputLength n))) :
    runChallenge distribution (fun challenge =>
      Masking.output (Masking.compile side W.program)
        (Masking.initial (Masking.compile side W.program) (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) (G.reductionTime time n)) =
    runChallenge distribution (fun challenge => (G.reduce (F n) side (A n) challenge).map some) := by
  unfold runChallenge
  congr 1
  funext challenge
  exact congrArg (fun p : ProbComp (Option Bool) =>
    p.map (fun result => (⟨result, [challenge]⟩ : ChallengeOutcome (G.outputLength n) (Option Bool))))
    ((G.mapWitness time side F A W).realizes n challenge)

/-- A reviewable certificate for both emitted programs and the joint loss. -/
structure ResourceReduction (G : Generator) (time : Nat → Nat) where
  left : ∀ F A, G.NativeWitness time F A →
    G.ChallengeWitness (G.reductionTime time) F (fun n => G.reduce (F n) false (A n))
  right : ∀ F A, G.NativeWitness time F A →
    G.ChallengeWitness (G.reductionTime time) F (fun n => G.reduce (F n) true (A n))
  left_code : ∀ F A W, (left F A W).code = (reductionPrograms W.program).1
  right_code : ∀ F A W, (right F A W).code = (reductionPrograms W.program).2
  advantage : ∀ n I A, G.encryptionGoal.advantage n I A ≤
    G.prgGoal.advantage n I (G.reduce I false A) +
      G.prgGoal.advantage n I (G.reduce I true A)

def resourceReduction (G : Generator) (time : Nat → Nat) : G.ResourceReduction time where
  left := G.mapWitness time false
  right := G.mapWitness time true
  left_code := by intros; rfl
  right_code := by intros; rfl
  advantage := G.advantage_le

/-- Concrete resource security: PRG security at the emitted programs' whole
runtime implies one-time encryption security at the original native runtime.
Both branches sample one PRG challenge, and the total loss is 2ε. -/
theorem resource_secure (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F ε) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass time) F (fun n => 2 * ε n) := by
  intro A ⟨W⟩ n
  have hl := h (fun n => G.reduce (F n) false (A n))
    ⟨(G.resourceReduction time).left F A W⟩ n
  have hr := h (fun n => G.reduce (F n) true (A n))
    ⟨(G.resourceReduction time).right F A W⟩ n
  exact ((G.resourceReduction time).advantage n (F n) (A n)).trans
    (by simpa [two_mul, advantageProfile] using add_le_add hl hr)

/-- The explicit reduction overhead preserves polynomial running time. -/
theorem reductionTime_polynomial (G : Generator) {time : Nat → Nat}
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength) :
    PolynomiallyBounded (G.reductionTime time) :=
  (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add
    ((PolynomiallyBounded.const 10).mul hL)).add (PolynomiallyBounded.const 9) |>.add ht

/-- Asymptotic security uses the two reductions' individual negligible
bounds. It does not assume a common negligible bound for every attack. -/
theorem resource_secure_asymptotic (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal)
    (h : SecureOnWithin G.prgGoal (G.challengeClass (G.reductionTime time)) F) :
    SecureOnWithin G.encryptionGoal (G.nativeClass time) F := by
  intro A ⟨W⟩
  have hl := h (fun n => G.reduce (F n) false (A n))
    ⟨(G.resourceReduction time).left F A W⟩
  have hr := h (fun n => G.reduce (F n) true (A n))
    ⟨(G.resourceReduction time).right F A W⟩
  exact Negligible.mono (fun n => G.advantage_le n (F n) (A n)) (hl.add hr)

end Generator
end Foundation.Symmetric
