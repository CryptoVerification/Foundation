import Foundation.Constructions.Symmetric.OneTimePad
import Foundation.Crypto.Semantics.Security.ThreeGames

/-! One-time left/right encryption from a pseudorandom generator. Messages
are fixed public instances, chosen before the fresh key/challenge. This is a
single-ciphertext notion, not adaptive multi-query chosen-plaintext security.
The generator's security is a hypothesis, not a conclusion about a concrete G. -/
namespace Foundation.Symmetric

open Foundation.Probability CryptoLogic
open scoped ENNReal

structure Generator where
  seedLength : Nat → Nat
  outputLength : Nat → Nat
  generate : ∀ n, Bits (seedLength n) → Bits (outputLength n)

namespace Generator

noncomputable def real (G : Generator) (n : Nat) : ProbComp (Bits (G.outputLength n)) :=
  (uniform (Bits (G.seedLength n))).map (G.generate n)

noncomputable def ideal (G : Generator) (n : Nat) : ProbComp (Bits (G.outputLength n)) :=
  uniform (Bits (G.outputLength n))

def encrypt (G : Generator) (n : Nat) (key : Bits (G.seedLength n))
    (message : Bits (G.outputLength n)) : Bits (G.outputLength n) :=
  Bits.xor (G.generate n key) message

def decrypt (G : Generator) (n : Nat) (key : Bits (G.seedLength n))
    (ciphertext : Bits (G.outputLength n)) : Bits (G.outputLength n) :=
  Bits.xor (G.generate n key) ciphertext

@[simp] theorem correctness (G : Generator) (n : Nat) (key : Bits (G.seedLength n))
    (message : Bits (G.outputLength n)) :
    G.decrypt n key (G.encrypt n key message) = message := Bits.xor_self_cancel _ _

abbrev Messages (G : Generator) (n : Nat) := Bits (G.outputLength n) × Bits (G.outputLength n)
abbrev Observer (G : Generator) (n : Nat) := Bits (G.outputLength n) → ProbComp Bool

def message (G : Generator) {n : Nat} (I : G.Messages n) (side : Bool) :
    Bits (G.outputLength n) := if side then I.2 else I.1

noncomputable def ciphertext (G : Generator) (n : Nat) (message : Bits (G.outputLength n)) :
    ProbComp (Bits (G.outputLength n)) := (G.real n).map (Bits.xor message)

theorem ciphertext_eq_encrypt (G : Generator) (n : Nat) (message : Bits (G.outputLength n)) :
    G.ciphertext n message =
      (uniform (Bits (G.seedLength n))).map (fun key => G.encrypt n key message) := by
  rw [ciphertext, real, PMF.map_comp]
  congr 1
  funext key
  exact Bits.xor_comm _ _

/-- An explicitly recorded single challenge query. Private native random
bits are not PRG queries; the generator experiment is consulted exactly once. -/
structure ChallengeOutcome (length : Nat) (Result : Type) where
  result : Result
  trace : List (Bits length)

noncomputable def runChallenge {Result : Type} {length : Nat} (distribution : ProbComp (Bits length))
    (observer : Bits length → ProbComp Result) : ProbComp (ChallengeOutcome length Result) :=
  distribution.bind fun challenge => (observer challenge).map fun result => ⟨result, [challenge]⟩

theorem runChallenge_result {Result : Type} {length : Nat} (distribution : ProbComp (Bits length))
    (observer : Bits length → ProbComp Result) :
    (runChallenge distribution observer).map ChallengeOutcome.result = distribution.bind observer := by
  rw [runChallenge, PMF.map_bind]
  congr 1
  funext challenge
  rw [PMF.map_comp]
  exact PMF.map_id _

/-- The bound is about the actual trace of every possible execution. -/
theorem runChallenge_queries {Result : Type} {length : Nat} (distribution : ProbComp (Bits length))
    (observer : Bits length → ProbComp Result) (outcome : ChallengeOutcome length Result)
    (h : outcome ∈ (runChallenge distribution observer).support) : outcome.trace.length = 1 := by
  rw [runChallenge, PMF.mem_support_bind_iff] at h
  obtain ⟨challenge, _, h⟩ := h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨bit, _, rfl⟩ := h
  rfl

/-- PRG security with public auxiliary messages. The challenge law does not
depend on them, but a uniform reduction is permitted to read them. -/
noncomputable def prgGoal (G : Generator) : CryptoGoal where
  Instance := G.Messages
  Adversary := fun n _ => G.Observer n
  advantage n _ A := probabilityGap (eventProb ((G.real n).bind A) (· = true))
    (eventProb ((G.ideal n).bind A) (· = true))

/-- Distinguishing one encryption of the left message from one encryption
of the equal-length right message, each using a fresh uniform seed. -/
noncomputable def encryptionGoal (G : Generator) : CryptoGoal where
  Instance := G.Messages
  Adversary := fun n _ => G.Observer n
  advantage n I A := probabilityGap (eventProb ((G.ciphertext n I.1).bind A) (· = true))
    (eventProb ((G.ciphertext n I.2).bind A) (· = true))

def reduce (G : Generator) {n : Nat} (I : G.Messages n) (side : Bool)
    (A : G.Observer n) : G.Observer n := fun challenge => A (Bits.xor (G.message I side) challenge)

noncomputable def branch (G : Generator) (side : Bool) :
    AdversaryTransform G.encryptionGoal G.prgGoal where
  mapInstance := id
  reduce := fun I A => G.reduce I side A

theorem real_reduce (G : Generator) (n : Nat) (I : G.Messages n) (side : Bool)
    (A : G.Observer n) :
    (G.real n).bind (G.reduce I side A) = (G.ciphertext n (G.message I side)).bind A := by
  rw [ciphertext, PMF.bind_map]
  rfl

theorem ideal_reduce (G : Generator) (n : Nat) (I : G.Messages n) (side : Bool)
    (A : G.Observer n) :
    (G.ideal n).bind (G.reduce I side A) = (G.ideal n).bind A := by
  have h := Bits.uniform_xor (G.message I side)
  have hb := congrArg (fun p => p.bind A) h
  rw [PMF.bind_map] at hb
  exact hb

/-- Both independently executable reductions are required. The loss uses
our probability-gap convention; it is the sum of their PRG advantages. -/
theorem advantage_le (G : Generator) (n : Nat) (I : G.Messages n) (A : G.Observer n) :
    G.encryptionGoal.advantage n I A ≤
      G.prgGoal.advantage n I (G.reduce I false A) +
      G.prgGoal.advantage n I (G.reduce I true A) := by
  change probabilityGap _ _ ≤ probabilityGap _ _ + probabilityGap _ _
  rw [real_reduce, real_reduce, ideal_reduce, ideal_reduce]
  have ht := CryptoLogic.ThreeGames.probabilityGap_triangle
    (eventProb ((G.ciphertext n I.1).bind A) (· = true))
    (eventProb ((G.ideal n).bind A) (· = true))
    (eventProb ((G.ciphertext n I.2).bind A) (· = true))
  simpa [message, probabilityGap, max_comm] using ht

end Generator
end Foundation.Symmetric
