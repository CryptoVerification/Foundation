import Foundation.Quantum.Mixture
import Foundation.Quantum.RecordObservation
import Foundation.Quantum.QKD.BB84Sampling

/-! Randomized block BB84 through the raw-key test. Uniform private bits and
independent uniform bases precede the arbitrary block channel. The test mask
is sampled freshly after sifting. Insufficient matched positions force abort.
The resulting density retains both private raw keys, public transcript and
Eve's quantum system. Error correction and privacy amplification remain separate. -/
namespace Foundation.Quantum.QKD.Randomized
noncomputable section
open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

structure Seed (n : Nat) where
  alice : Fin n → BB84Basis
  bob : Fin n → BB84Basis
  bits : Fin n → Fin 2
  deriving Fintype, DecidableEq

instance (n : Nat) : Nonempty (Seed n) := ⟨⟨(fun _ => .Z), (fun _ => .Z), (fun _ => 0)⟩⟩

structure Configuration (n : Nat) where
  seed : Seed n
  tested : Finset (Fin n)
  deriving Fintype, DecidableEq

/-- All private input bits and both basis strings are uniformly sampled. -/
def seedDistribution (n : Nat) : ProbComp (Seed n) := uniform (Seed n)

/-- A fresh uniform test mask, or the empty mask on an insufficient population. -/
def testDistribution {n : Nat} (s : Seed n) (k : Nat) : ProbComp (Finset (Fin n)) :=
  if hk : k ≤ (RawProtocol.matched s.alice s.bob).card then
    Sampling.sample (RawProtocol.matched s.alice s.bob) k hk else PMF.pure ∅

def configurationDistribution (n k : Nat) : ProbComp (Configuration n) :=
  (seedDistribution n).bind (fun s => (testDistribution s k).map (fun T => ⟨s,T⟩))

/-- Raising the minimum beyond the population forces abort when the requested sample is impossible. -/
def requiredLength {n : Nat} (s : Seed n) (k minKey : Nat) : Nat :=
  if k ≤ (RawProtocol.matched s.alice s.bob).card then minKey
  else (RawProtocol.matched s.alice s.bob).card + 1

def rawOutput {n : Nat} (c : Configuration n) (k minKey tolerance : Nat)
    (bobBits : Fin n → Fin 2) : RawProtocol.Output n :=
  RawProtocol.output c.seed.alice c.seed.bob c.seed.bits bobBits c.tested
    (requiredLength c.seed k minKey) tolerance

theorem insufficient_abort {n : Nat} (c : Configuration n) (k minKey tolerance : Nat)
    (bobBits : Fin n → Fin 2) (hk : ¬ k ≤ (RawProtocol.matched c.seed.alice c.seed.bob).card) :
    (rawOutput c k minKey tolerance bobBits).transcript.accepted = false := by
  have hc : (RawProtocol.keyPositions c.seed.alice c.seed.bob c.tested).card ≤
      (RawProtocol.matched c.seed.alice c.seed.bob).card :=
    Finset.card_le_card Finset.sdiff_subset
  simp only [rawOutput, RawProtocol.output, RawProtocol.accepts, requiredLength, if_neg hk]
  simp only [decide_eq_false_iff_not]
  omega

theorem insufficient_empty_keys {n : Nat} (c : Configuration n) (k minKey tolerance : Nat)
    (bobBits : Fin n → Fin 2) (hk : ¬ k ≤ (RawProtocol.matched c.seed.alice c.seed.bob).card) :
    (rawOutput c k minKey tolerance bobBits).aliceKey = (fun _ => none) ∧
      (rawOutput c k minKey tolerance bobBits).bobKey = (fun _ => none) :=
  RawProtocol.abort_keys _ _ _ _ _ _ _ (insufficient_abort c k minKey tolerance bobBits hk)

/-- The actual conditional state, including the abort guard. -/
def conditionalRecord {n : Nat} {e : Space} (A : BlockAttack n e)
    (c : Configuration n) (k minKey tolerance : Nat) :
    Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) (.tensor (qubits n) e)) :=
  RawProtocol.record A c.seed.alice c.seed.bob c.seed.bits c.tested
    (requiredLength c.seed k minKey) tolerance

/-- All classical choices are averaged as actual density operators, not as independent Eve marginals. -/
def record {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) (.tensor (qubits n) e)) :=
  Density.mixture (configurationDistribution n k) (fun c => conditionalRecord A c k minKey tolerance)

/-- Joint private raw keys, public transcript and Eve, after discarding Bob's remaining quantum system.
This is the state interface for subsequent error correction and privacy amplification. -/
def keyState {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e) :=
  (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
    (record A k minKey tolerance)

theorem keyState_mixture {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (keyState A k minKey tolerance).matrix =
      (Density.mixture (configurationDistribution n k) (fun c =>
        (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
          (conditionalRecord A c k minKey tolerance))).matrix :=
  Density.mixture_channel _ _ _

/-- The public transcript remains jointly correlated with Eve after forgetting private keys and Bob's quantum output. -/
def publicState {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Density (.tensor (.register (Fintype.card (RawProtocol.PublicRecord n))) e) :=
  (RawProtocol.publicChannel n e).run (record A k minKey tolerance)

theorem publicState_mixture {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (publicState A k minKey tolerance).matrix =
      (Density.mixture (configurationDistribution n k) (fun c =>
        RawProtocol.publicState A c.seed.alice c.seed.bob c.seed.bits c.tested
          (requiredLength c.seed k minKey) tolerance)).matrix :=
  Density.mixture_channel _ _ _

theorem record_normalized {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (record A k minKey tolerance).matrix.trace = 1 := (record A k minKey tolerance).normalized

theorem public_observation {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat)
    (E : Effect (.tensor (.register (Fintype.card (RawProtocol.PublicRecord n))) e)) :
    E.probability (publicState A k minKey tolerance) =
      ∑ c, (configurationDistribution n k c).toReal *
        E.probability (RawProtocol.publicState A c.seed.alice c.seed.bob c.seed.bits c.tested
          (requiredLength c.seed k minKey) tolerance) := by
  unfold Effect.probability
  rw [publicState_mixture]
  exact Density.mixture_observation _ _ E

/-- Existing ProbComp output retains the same physical measurement labels and explicit classical postprocessing. -/
def outcome {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    ProbComp (RawProtocol.Output n) :=
  (configurationDistribution n k).bind (fun c =>
    (A.outcome c.seed.alice c.seed.bob c.seed.bits).map
      (fun r => rawOutput c k minKey tolerance (blockOutcomeBits n r)))


theorem conditional_record_event {n : Nat} {e : Space} (A : BlockAttack n e)
    (c : Configuration n) (k minKey tolerance : Nat) (P : RawProtocol.Output n → Prop)
    [DecidablePred P] :
    (recordEvent (.tensor (qubits n) e)
      (fun r => P ((Fintype.equivFin (RawProtocol.Output n)).symm r))).probability
      (conditionalRecord A c k minKey tolerance) =
      (eventProb ((A.outcome c.seed.alice c.seed.bob c.seed.bits).map
        (fun r => rawOutput c k minKey tolerance (blockOutcomeBits n r))) P).toReal :=
  Instrument.encoded_record_event ((blockMeasurement n c.seed.bob).amplify e)
    (A.jointState c.seed.alice c.seed.bits) _ P

/-- The fully randomized density and the existing probabilistic execution have exactly the same classical observations. -/
theorem record_event {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat)
    (P : RawProtocol.Output n → Prop) [DecidablePred P] :
    (recordEvent (.tensor (qubits n) e)
      (fun r => P ((Fintype.equivFin (RawProtocol.Output n)).symm r))).probability
      (record A k minKey tolerance) = (eventProb (outcome A k minKey tolerance) P).toReal := by
  rw [record, Density.mixture_observation, outcome, eventProb_bind_toReal]
  apply Finset.sum_congr rfl
  intro c _
  rw [conditional_record_event]

end
end Foundation.Quantum.QKD.Randomized
