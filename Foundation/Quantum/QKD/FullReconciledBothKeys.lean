import Foundation.Quantum.QKD.FullReconciledHash
import Foundation.Quantum.QKD.VerifiedHashBothKeys

/-! Actual decoded Bob key and original Alice key are hashed locally with
one independent PA seed. The public packet includes the complete reconciliation
message. Fresh verifier collision bounds do not assume successful decoding. -/
namespace Foundation.Quantum.QKD.FullReconciledHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def bothFixed {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e)
    (s : Hashing.RawSeed n tag) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict (restrict ρ (fun o => o.transcript.accepted = true))
      (fun o => Hashing.rawHash s o.aliceKey = Hashing.rawHash s (FullRawReconciliation.output o).bobKey)))
    (fun ro => ((Hashing.rawHash ro.1 ro.2.aliceKey,Hashing.rawHash ro.1 (FullRawReconciliation.output ro.2).bobKey),
      ((((ro.2.transcript,FullRawReconciliation.publicMessage ro.2),s),Hashing.rawHash s ro.2.aliceKey),ro.1)))

def bothAverage {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :=
  mixture (Foundation.Probability.uniform (Hashing.RawSeed n tag)) (fun s => bothFixed (length := length) ρ s)

theorem bothFixed_alice {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e)
    (s : Hashing.RawSeed n tag) : CommonKey.aliceView (bothFixed (length := length) ρ s) = fixed (length := length) ρ s := by
  unfold CommonKey.aliceView bothFixed fixed
  rw [relabel_comp]
  rfl

theorem bothAverage_alice {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :
    CommonKey.aliceView (bothAverage (tag := tag) (length := length) ρ) = average (tag := tag) (length := length) ρ := by
  unfold CommonKey.aliceView bothAverage average
  rw [mixture_relabel]
  congr 1
  funext s
  exact bothFixed_alice ρ s

def checkedInput {n : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :=
  relabel (restrict ρ (fun o => o.transcript.accepted = true))
    (fun o => ((o.aliceKey,(FullRawReconciliation.output o).bobKey),(o.transcript,FullRawReconciliation.publicMessage o)))

/-- This is the earlier actual fresh-seed verification followed by local PA,
with the same tag and public seeds, at the same original branch weights. -/
theorem bothAverage_verifier {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :
    bothAverage (tag := tag) (length := length) ρ =
      VerifiedHash.pairHash (KeyVerification.accepted (checkedInput ρ)
        (Foundation.Probability.uniform (Hashing.RawSeed n tag)) Hashing.rawHash)
        (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash := by
  unfold VerifiedHash.pairHash
  rw [KeyVerification.accepted_mixture, mixture_seed, mixture_relabel]
  unfold bothAverage
  congr 1
  funext s
  unfold KeyVerification.selected checkedInput
  rw [restrict_relabel, seed_relabel, seed_relabel, relabel_comp, relabel_comp]
  rfl

theorem bothAverage_correctness {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :
    CommonKey.correctnessError (bothAverage (tag := tag) (length := length) ρ) ≤
      1 / Fintype.card (IdealKey.Key tag) := by
  rw [bothAverage_verifier]
  apply le_trans (VerifiedHash.pairHash_correctness _ _ _)
  exact KeyVerification.correctness_budget _ _ _ _ (by positivity)
    (fun a b hab => le_of_eq (Collision.raw_collision a b hab))

/-- A sharper bound retains the actual probability of decoder mismatch. -/
theorem bothAverage_correctness_weighted {n tag length : Nat} {e : Space}
    (ρ : State (RawProtocol.Output n) e) :
    CommonKey.correctnessError (bothAverage (tag := tag) (length := length) ρ) ≤
      (1 / Fintype.card (IdealKey.Key tag)) * CommonKey.correctnessError (checkedInput ρ) := by
  rw [bothAverage_verifier]
  apply le_trans (VerifiedHash.pairHash_correctness _ _ _)
  exact KeyVerification.correctness_le _ _ _ _
    (fun a b hab => le_of_eq (Collision.raw_collision a b hab))

end
end Foundation.Quantum.QKD.FullReconciledHash
