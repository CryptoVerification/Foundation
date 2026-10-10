import Foundation.Quantum.QKD.PairwiseRawCertificate
import Foundation.Quantum.QKD.BB84Collision

/-! The remaining key uses exactly the optional position-labelled key format
of the actual raw protocol, and can use its existing binary-matrix hash. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

def optionalKey {n : Nat} (T : Finset (Fin n))
    (x : (qubits (BB84SiftedInput.remainderCount T)).Basis) : Finalization.RawKey n :=
  fun i => if h : i ∈ T then none
    else some (readBits x ((BB84SiftedInput.remainderIndex T).symm ⟨i,h⟩))

theorem optionalKey_injective {n : Nat} (T : Finset (Fin n)) : Function.Injective (optionalKey T) := by
  intro x y h
  apply (bitStringEquiv _).injective
  funext i
  change readBits x i = readBits y i
  have hi : (BB84SiftedInput.remainderIndex T).symm
      ⟨(BB84SiftedInput.remainderIndex T i).val, (BB84SiftedInput.remainderIndex T i).property⟩ = i :=
    (BB84SiftedInput.remainderIndex T).symm_apply_apply i
  have hh := congrFun h (BB84SiftedInput.remainderIndex T i).val
  simpa only [optionalKey, (BB84SiftedInput.remainderIndex T i).property,
    dite_false, hi, Option.some.injEq] using hh

theorem optionalKey_split {n : Nat} (T : Finset (Fin n)) (x : (qubits n).Basis) :
    optionalKey T (testEquiv T x).1 = (fun i => if i ∈ T then none else some (readBits x i)) := by
  funext i
  by_cases hi : i ∈ T
  · simp only [optionalKey, hi, dite_true, ite_true]
  · simp only [optionalKey, hi, dite_false, ite_false]
    congr 1
    rw [remaining_bits]
    simp only [Equiv.apply_symm_apply]

theorem decoded_alice_key {n : Nat} (θ : Fin n → BB84Basis) (T : Finset (Fin n))
    (minKey tolerance : Nat) (r z : (qubits n).Basis)
    (hr : BB84DelayedDecision.accepts T minKey tolerance (errorCode r)) :
    (decodeRawLabel θ T minKey tolerance (errorCode r,errorCode z)).aliceKey =
      optionalKey T (testEquiv T (alice n θ r z)).1 := by
  have ha := decoded_acceptance θ T minKey tolerance (errorCode r) (errorCode z)
  have hac : RawProtocol.accepts θ θ
      (readBits (BB84OutcomeCoordinates.originalOutcomes θ (errorCode r,errorCode z)).2)
      (readBits (BB84OutcomeCoordinates.originalOutcomes θ (errorCode r,errorCode z)).1)
      T minKey tolerance = true := by
    simpa only [decodeRawLabel, BB84DeferredRaw.recoverLabel, BB84DeferredRaw.rawLabel,
      Equiv.symm_apply_apply, RawProtocol.output, hr, decide_true] using ha
  rw [optionalKey_split]
  funext i
  simp only [decodeRawLabel, BB84DeferredRaw.recoverLabel, BB84DeferredRaw.rawLabel,
    Equiv.symm_apply_apply, RawProtocol.output, hac]
  simp [RawProtocol.keyPositions, RawProtocol.matched, original_alice]

def remainingHash {n length : Nat} (T : Finset (Fin n)) (s : Hashing.RawSeed n length)
    (x : (qubits (BB84SiftedInput.remainderCount T)).Basis) : IdealKey.Key length :=
  Hashing.rawHash s (optionalKey T x)

theorem remaining_collision {n length : Nat} (T : Finset (Fin n))
    (x y : (qubits (BB84SiftedInput.remainderCount T)).Basis) (hxy : x ≠ y) :
    Collision.collision (Foundation.Probability.uniform (Hashing.RawSeed n length)) (remainingHash T) x y ≤
      1 / Fintype.card (IdealKey.Key length) :=
  le_of_eq (Collision.raw_collision (optionalKey T x) (optionalKey T y)
    (fun h => hxy (optionalKey_injective T h)))

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
