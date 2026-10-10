import Foundation.Quantum.QKD.BB84PairwiseMeasurement

/-! The uniform BB84 basis string is precisely a uniform one-out-of-two
selector on the fixed-reference pairs. The complementary coordinates stay
quantum until the separate key-side gate and measurement. -/
namespace Foundation.Quantum.QKD.BB84PairwiseReference
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

def selectBit : BB84Basis → Fin 2
  | .Z => 0
  | .X => 1

def selection {n : Nat} (θ : Fin n → BB84Basis) : Fin n → Fin 2 := fun i => selectBit (θ i)

def selectorEquiv (n : Nat) : (Fin n → BB84Basis) ≃ (Fin n → Fin 2) where
  toFun := selection
  invFun b i := if b i = 0 then .Z else .X
  left_inv θ := by funext i; cases h : θ i <;> simp [selection, selectBit, h]
  right_inv b := by
    funext i
    by_cases h : b i = 0
    · simp [selection, selectBit, h]
    · have h1 : b i = 1 := by omega
      simp [selection, selectBit, h1]

def pairBits {n : Nat} (p : (Space.tensor (qubits n) (qubits n)).Basis) :
    Fin n × Fin 2 → Fin 2 := fun ij => if ij.2 = 0 then readBits p.1 ij.1 else readBits p.2 ij.1

theorem selected_bits {n : Nat} (θ : Fin n → BB84Basis)
    (p : (Space.tensor (qubits n) (qubits n)).Basis) (i : Fin n) :
    errorBits θ p i = pairBits p (i,selection θ i) := by
  cases h : θ i <;> simp [errorBits, pairBits, selection, selectBit, h]

theorem complementary_bits {n : Nat} (θ : Fin n → BB84Basis)
    (p : (Space.tensor (qubits n) (qubits n)).Basis) (i : Fin n) :
    keyBits θ p i = pairBits p (i,selectBit (BB84SiftingRandomness.opposite (θ i))) := by
  cases h : θ i <;> simp [keyBits, pairBits, selectBit, BB84SiftingRandomness.opposite, h]

/-- The actual unnormalized reference branch is taken from one basis-independent
input. Its later gate does not affect which error branch was recorded. -/
theorem reference_branch {n : Nat} {e : Space} (ρ : Density (jointSpace n e))
    (θ : Fin n → BB84Basis) (r : Fin (count n)) :
    ((referenceFirst θ e).branch r).apply ρ.matrix =
      ((keyChannel θ).amplify e).toKraus.apply
        (((PartitionMeasurement.instrument (errorLabel θ (e := e))).branch r).apply
          (referenceInput ρ).matrix) := by
  simp only [referenceFirst, Instrument.pre_apply, Instrument.post_apply, Channel.seq, Kraus.seq_apply]
  rfl

/-- Replacing uniform basis strings by uniform binary selectors changes no
joint output state, for any finite quantum family. -/
theorem uniform_selector {n : Nat} {a : Space} (F : (Fin n → Fin 2) → Density a) :
    (Density.mixture (Foundation.Probability.uniform (Fin n → BB84Basis))
      (fun θ => F (selection θ))).matrix =
      (Density.mixture (Foundation.Probability.uniform (Fin n → Fin 2)) F).matrix :=
  Density.mixture_uniform_equiv (selectorEquiv n) F

end
end Foundation.Quantum.QKD.BB84PairwiseReference
