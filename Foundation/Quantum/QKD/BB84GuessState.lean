import Foundation.Quantum.QKD.CQRelabel
import Foundation.Quantum.QKD.GuessLogic
import Foundation.Quantum.QKD.GuessPublic
import Foundation.Quantum.QKD.GuessAdditionalLeak
import Foundation.Quantum.ClassicalComposition
import Foundation.Quantum.ClassicalDiscard
import Foundation.Quantum.Distinguishability

/-! The actual randomized BB84 state as Alice's raw key, the full public
transcript (including abort), and Eve's quantum register. Bob's private key
is discarded rather than disclosed to Eve. This does not supply a phase-error
or secrecy bound for BB84. -/
namespace Foundation.Quantum.QKD.RawGuess
noncomputable section
open Guessing
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

abbrev Key (n : Nat) := Fin n → Option (Fin 2)
abbrev Label (n : Nat) := Key n × RawProtocol.PublicRecord n

def label {n : Nat} (t : Fin (Fintype.card (RawProtocol.Output n))) : Label n :=
  let o := (Fintype.equivFin (RawProtocol.Output n)).symm t
  (o.aliceKey,o.transcript)

/-- No conditioning on acceptance: the abort alternative stays in the state. -/
def state {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) : CQ (Label n) e :=
  relabel (bb84Blocks A k minKey tolerance) label

/-- This CQ state is produced by a real physical channel from the old joint output. -/
theorem state_physical {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (state A k minKey tolerance).density.matrix =
      ((classicalMap e (fun t => Fintype.equivFin (Label n) (label t))).run
        (Randomized.keyState A k minKey tolerance)).matrix :=
  read_relabel_physical _ _

/-- The public part is exactly the previously implemented public BB84 state,
not a separately chosen distribution or an independent Eve marginal. -/
theorem public_state {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (relabel (state A k minKey tolerance) Prod.snd).density.matrix =
      (Randomized.publicState A k minKey tolerance).matrix := by
  rw [relabel_physical]
  change (classicalMap e _).toKraus.apply (state A k minKey tolerance).density.matrix = _
  rw [state_physical]
  change (classicalMap e _).toKraus.apply ((classicalMap e _).toKraus.apply
    (Randomized.keyState A k minKey tolerance).matrix) = _
  rw [classicalMap_compose]
  have hfun : (fun t => Fintype.equivFin (RawProtocol.PublicRecord n)
      (((Fintype.equivFin (Label n)).symm t).2)) ∘
      (fun t => Fintype.equivFin (Label n) (label t)) =
      (fun t => Fintype.equivFin (RawProtocol.PublicRecord n)
        (((Fintype.equivFin (RawProtocol.Output n)).symm t).transcript)) := by
    funext t
    simp [Function.comp_apply, label]
  rw [hfun]
  unfold Randomized.publicState RawProtocol.publicChannel
  rw [Channel.seq_run_matrix]
  change _ = (discardMiddle _ _ _).toKraus.apply ((classicalMap _ _).toKraus.apply _)
  rw [classicalMap_discardMiddle]
  rfl

/-- All complete measurements may depend on the actual public record. -/
def probability {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) : ℝ :=
  leakedGuessingProbability (state A k minKey tolerance)

/-- Optimal guessing using arbitrary measurements of the full public-and-quantum
side system agrees with the public-dependent strategy definition. -/
theorem probability_joint {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    guessingProbability (withPublic (state A k minKey tolerance)) =
      probability A k minKey tolerance := withPublic_optimal _

/-- A generic public-information bound, without claiming that this large
transcript alphabet gives a useful finite-key security estimate. -/
theorem transcript_cost {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    probability A k minKey tolerance ≤ Fintype.card (RawProtocol.PublicRecord n) *
      guessingProbability (hideLeak (state A k minKey tolerance)) :=
  leakage_chain _

/-- A concrete positive-operator certificate on this actual state can be
interpreted through the existing composite derivation. The certificate itself
is not an assumed theorem about arbitrary BB84 attacks. -/
theorem interpreted_bound {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat)
    (σ : Density e) (q : ℝ) (h : Dominated (hideLeak (state A k minKey tolerance)) σ q) :
    probability A k minKey tolerance ≤ Fintype.card (RawProtocol.PublicRecord n) * q := by
  exact GuessLogic.sound (fun _ => state A k minKey tolerance) (fun _ => σ)
    (GuessLogic.leakProof (Fintype.card (RawProtocol.PublicRecord n)) 0 0 q) (fun _ => h)

/-- A concrete reconciliation message may depend on Alice's raw key and
all previous public data. Its guessing cost uses only the new alphabet. -/
theorem message_cost {n : Nat} {e : Space} {C : Type} [Fintype C] [DecidableEq C]
    (A : BlockAttack n e) (k minKey tolerance : Nat)
    (message : Key n → RawProtocol.PublicRecord n → C) :
    leakedGuessingProbability (withPublic (disclose (state A k minKey tolerance) message)) ≤
      Fintype.card C * probability A k minKey tolerance :=
  disclosure_cost _ _

end
end Foundation.Quantum.QKD.RawGuess
