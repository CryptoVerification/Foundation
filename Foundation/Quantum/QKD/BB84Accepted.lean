import Foundation.Quantum.QKD.BB84GuessState
import Foundation.Quantum.QKD.SubnormalizedRelabel

/-! The accepted branch of the actual randomized BB84 output. Its trace is
the actual acceptance probability; guessing is success per original execution,
not conditioned by dividing through acceptance. Eve keeps all public data. -/
namespace Foundation.Quantum.QKD.Accepted
noncomputable section
open Guessing
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

/-- Rejected outputs have zero block; the accepted blocks keep their original weight. -/
def state {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Subnormalized.State (RawGuess.Label n) e :=
  Subnormalized.restrict (Subnormalized.ofCQ (RawGuess.state A k minKey tolerance))
    (fun p => p.2.accepted = true)

theorem physical {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Subnormalized.joint (state A k minKey tolerance) =
      (Subnormalized.eventFilter (fun p : RawGuess.Label n => p.2.accepted = true)).apply
        (RawGuess.state A k minKey tolerance).density.matrix :=
  Subnormalized.restrict_physical _ _

/-- The branch mass is the probability of the actual BB84 acceptance test. -/
theorem mass_acceptance {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Subnormalized.mass (state A k minKey tolerance) =
      (recordEvent e (fun t => (((Fintype.equivFin (RawProtocol.Output n)).symm t).transcript.accepted = true))).probability
        (Randomized.keyState A k minKey tolerance) := by
  unfold state
  rw [Subnormalized.restrict_mass_probability]
  change (_ * (RawGuess.state A k minKey tolerance).density.matrix).trace.re = _
  rw [RawGuess.state_physical]
  change (recordEvent e (fun t => (((Fintype.equivFin (RawGuess.Label n)).symm t).2.accepted = true))).probability
    ((classicalMap e (fun t => Fintype.equivFin (RawGuess.Label n) (RawGuess.label t))).run
      (Randomized.keyState A k minKey tolerance)) = _
  rw [Effect.probability_run]
  unfold Effect.probability
  rw [classicalMap_recordEvent]
  simp only [Equiv.symm_apply_apply, RawGuess.label]

/-- Joint measurements of the entire public transcript and Eve's system. -/
def probability {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) : ℝ :=
  Subnormalized.probability (Subnormalized.withPublic (state A k minKey tolerance))

theorem probability_le_acceptance {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    probability A k minKey tolerance ≤
      (recordEvent e (fun t => (((Fintype.equivFin (RawProtocol.Output n)).symm t).transcript.accepted = true))).probability
        (Randomized.keyState A k minKey tolerance) := by
  rw [← mass_acceptance]
  exact Subnormalized.public_probability_le_mass _

/-- Zero-probability acceptance requires no conditional state or division. -/
theorem probability_zero {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat)
    (h : Subnormalized.mass (state A k minKey tolerance) = 0) :
    probability A k minKey tolerance = 0 := by
  apply Subnormalized.probability_zero_mass
  simpa only [Subnormalized.mass_withPublic] using h

/-- Weighting by acceptance cannot improve success per original execution. -/
theorem probability_le_original {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    probability A k minKey tolerance ≤ RawGuess.probability A k minKey tolerance := by
  have h := Subnormalized.public_restrict_le (Subnormalized.ofCQ (RawGuess.state A k minKey tolerance))
    (fun p => p.2.accepted = true)
  rw [Subnormalized.withPublic_ofCQ, Subnormalized.probability_ofCQ, withPublic_optimal] at h
  exact h

/-- Additional reconciliation communication obeys the same multiplicative
cost on the accepted branch, without division by its probability. -/
theorem message_cost {n : Nat} {e : Space} {C : Type} [Fintype C] [DecidableEq C]
    (A : BlockAttack n e) (k minKey tolerance : Nat)
    (message : RawGuess.Key n → RawProtocol.PublicRecord n → C) :
    Subnormalized.probability (Subnormalized.withPublic (Subnormalized.withPublic
      (Subnormalized.disclose (state A k minKey tolerance) message))) ≤
      Fintype.card C * probability A k minKey tolerance :=
  Subnormalized.disclosure_cost _ _

end
end Foundation.Quantum.QKD.Accepted
