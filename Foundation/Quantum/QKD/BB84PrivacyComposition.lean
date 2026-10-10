import Foundation.Quantum.QKD.HashLayout
import Foundation.Quantum.QKD.BB84FinalSecurity
import Foundation.Quantum.QKD.BB84HashDistance

/-! The collision/leftover-hash bound and the actual two-key BB84 output are
now one experiment, after an explicitly proved basis-coordinate transport.
The input operator domination and correctness are separate obligations. -/
namespace Foundation.Quantum.QKD.FinalPrivacy
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
variable {n length : Nat} {S : Type} [Fintype S] [DecidableEq S] {e : Space}

/-- Discarding Bob's private key from the actual accepted final state gives
the exact fresh-public-seed hash of the earlier accepted Alice/transcript state. -/
theorem alice_output (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    CommonKey.aliceView (FinalSecurity.acceptedBranch A k minKey tolerance p hash) =
      HashLayout.output (Accepted.state A k minKey tolerance) p hash := by
  unfold CommonKey.aliceView FinalSecurity.acceptedBranch
  rw [relabel_comp]
  unfold HashLayout.output
  have ha : Accepted.state A k minKey tolerance =
      restrict (relabel (ofCQ (Guessing.bb84Blocks A k minKey tolerance)) RawGuess.label)
        (fun p => p.2.accepted = true) := rfl
  rw [ha, restrict_relabel, seed_relabel, seed_restrict, relabel_comp]
  rfl

/-- Both the two-key final branch and the earlier Alice-only branch keep
exactly the same acceptance mass. -/
theorem accepted_mass (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    mass (FinalSecurity.acceptedBranch A k minKey tolerance p hash) =
      mass (Accepted.state A k minKey tolerance) := by
  have h := congrArg mass (alice_output A k minKey tolerance p hash)
  simpa only [CommonKey.aliceView, HashLayout.output, mass_relabel, mass_seed] using h

/-- The mass used in the leftover-hash error is the actual final acceptance
probability, for every seed distribution and deterministic hash. -/
theorem input_mass_probability (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    mass (Collision.acceptedInput A k minKey tolerance) =
      (recordEvent e (fun r => let o : IdealKey.Output (Finalization.Transcript n S) length := (Fintype.equivFin _).symm r
        o.accepted = true)).probability (Finalization.state A k minKey tolerance p hash) := by
  rw [FinalSecurity.acceptance_probability, accepted_mass, Collision.acceptedInput, mass_withPublic]

/-- A proved domination certificate on the pre-hash accepted input gives the
actual final Alice-key secrecy judgment, retaining every public seed/transcript. -/
theorem secrecy (A : BlockAttack n e) (k minKey tolerance : Nat)
    (τ : Density (Guessing.publicSpace (RawProtocol.PublicRecord n) e))
    (q : ℝ) (hq : 0 ≤ q) (hdom : Dominated (Collision.acceptedInput A k minKey tolerance) τ q) :
    OperatorApprox
      (joint (CommonKey.aliceView (FinalSecurity.acceptedBranch A k minKey tolerance
        (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash)))
      (joint (CommonKey.uniformize (CommonKey.aliceView (FinalSecurity.acceptedBranch A k minKey tolerance
        (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash))))
      ((1/2:ℝ)*Real.sqrt ((Fintype.card (IdealKey.Key length) *
        (1 - 1/Fintype.card (IdealKey.Key length))) * q *
          mass (Collision.acceptedInput A k minKey tolerance))) := by
  rw [alice_output]
  exact HashLayout.secrecy (Accepted.state A k minKey tolerance)
    (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash _
    (by simpa only [mul_assoc, Collision.acceptedInput] using
      Collision.accepted_dominated_distance_general (length := length) A k minKey tolerance τ q hq hdom)

/-- Conditional security of the existing full BB84 hash output: the only
remaining premises here are pre-hash domination and actual correctness. The
fresh hash, full public information, Bob's key, Eve and abort are all retained. -/
theorem secure (A : BlockAttack n e) (k minKey tolerance : Nat)
    (τ : Density (Guessing.publicSpace (RawProtocol.PublicRecord n) e))
    (q δ : ℝ) (hq : 0 ≤ q) (hdom : Dominated (Collision.acceptedInput A k minKey tolerance) τ q)
    (hc : CommonKey.correctnessError (FinalSecurity.acceptedBranch A k minKey tolerance
      (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash) ≤ δ) :
    IdealKey.Secure (Finalization.state A k minKey tolerance
      (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash)
      (δ + (1/2:ℝ)*Real.sqrt ((Fintype.card (IdealKey.Key length) *
        (1 - 1/Fintype.card (IdealKey.Key length))) * q *
          mass (Collision.acceptedInput A k minKey tolerance))) :=
  FinalSecurity.secure A k minKey tolerance _ _ δ _ hc (secrecy A k minKey tolerance τ q hq hdom)

end
end Foundation.Quantum.QKD.FinalPrivacy
