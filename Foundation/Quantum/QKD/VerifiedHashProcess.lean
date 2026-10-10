import Foundation.Quantum.QKD.PairwiseVerificationPublicRaw
import Foundation.Quantum.QKD.CommonKeyProcessing
import Foundation.Quantum.QKD.ReadClassicalState

/-! The specified raw-key check and PA procedure on an arbitrary CQ input.
The same public fields are retained on accepted branches. No secrecy claim
is introduced by this definition; actual BB84 certificates supply the bound. -/
namespace Foundation.Quantum.QKD.VerifiedHash
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def fixed {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e)
    (s : Hashing.RawSeed n tag) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict (restrict ρ (fun o => o.transcript.accepted = true))
      (fun o => Hashing.rawHash s o.aliceKey = Hashing.rawHash s o.bobKey)))
    (fun ro => (Hashing.rawHash ro.1 ro.2.aliceKey,
      (((ro.2.transcript,s),Hashing.rawHash s ro.2.aliceKey),ro.1)))

def average {n tag length : Nat} {e : Space} (ρ : State (RawProtocol.Output n) e) :=
  mixture (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => fixed (length := length) ρ s)

/-- Read the actual joint density's classical raw-output blocks, then run
both specified independent seeded procedures. -/
def fromDensity {n tag length : Nat} {e : Space}
    (ρ : Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e)) :=
  average (tag := tag) (length := length) (readDensity ρ)

theorem post_fixed {n tag length : Nat} {a b : Space} (ρ : State (RawProtocol.Output n) a)
    (C : Channel a b) (s : Hashing.RawSeed n tag) :
    post (fixed (length := length) ρ s) C = fixed (length := length) (post ρ C) s := by
  unfold fixed
  rw [post_relabel, post_seed, post_restrict, post_restrict]

/-- The seed mixture commutes with a quantum-side channel, including partial
trace. This is a linear identity on every conditional matrix. -/
theorem post_mixture {S X : Type} [Fintype S] [Fintype X] {a b : Space}
    (p : PMF S) (ρ : S → State X a) (C : Channel a b) :
    post (mixture p ρ) C = mixture p (fun s => post (ρ s) C) := by
  apply State.ext
  funext x
  change C.toKraus.linear (∑ s, ((p s).toReal:ℂ) • (ρ s).block x) =
    ∑ s, ((p s).toReal:ℂ) • C.toKraus.linear ((ρ s).block x)
  rw [map_sum]
  simp only [map_smul]

theorem post_average {n tag length : Nat} {a b : Space} (ρ : State (RawProtocol.Output n) a)
    (C : Channel a b) :
    post (average (tag := tag) (length := length) ρ) C =
      average (tag := tag) (length := length) (post ρ C) := by
  unfold average
  rw [post_mixture]
  simp only [post_fixed]

end
end Foundation.Quantum.QKD.VerifiedHash

namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized PureProjection
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem verifiedRawHash_process {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (s : Hashing.RawSeed n tag) :
    verifiedRawHash (length := length) v hv k gap minKey tolerance c s =
      VerifiedHash.fixed (length := length) (ofCQ (rawState v hv k gap minKey tolerance c)) s := rfl

theorem verifiedRawAverage_process {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    verifiedRawAverage (tag := tag) (length := length) v hv k gap minKey tolerance c =
      VerifiedHash.average (tag := tag) (length := length) (ofCQ (rawState v hv k gap minKey tolerance c)) := rfl

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
