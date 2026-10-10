import Foundation.Quantum.QKD.BB84RandomSource

/-! Exact sifting randomness for the existing independent-basis BB84
experiment. The match set and Alice's basis string are independent uniform
choices. Their test distribution and insufficient-population guard retain
the existing definitions. Equalities concern full quantum records, not
independent or averaged Eve marginals. -/
namespace Foundation.Quantum.QKD.BB84SiftingRandomness
noncomputable section
set_option backward.isDefEq.respectTransparency false

local instance : Nonempty BB84Basis := ⟨.Z⟩

def opposite : BB84Basis → BB84Basis
  | .Z => .X
  | .X => .Z

def bobBases {n : Nat} (θ : Fin n → BB84Basis) (M : Finset (Fin n)) :
    Fin n → BB84Basis := fun i => if i ∈ M then θ i else opposite (θ i)

theorem matched_bob {n : Nat} (θ : Fin n → BB84Basis) (M : Finset (Fin n)) :
    RawProtocol.matched θ (bobBases θ M) = M := by
  ext i
  simp only [RawProtocol.matched, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : i ∈ M
  · simp [bobBases, h]
  · cases hθ : θ i <;> simp [bobBases, h, hθ, opposite]

/-- Each independent basis pair has exactly one match-set/basis description. -/
def basisEquiv (n : Nat) :
    ((Fin n → BB84Basis) × Finset (Fin n)) ≃ BB84RandomSource.Bases n where
  toFun p := ⟨p.1, bobBases p.1 p.2⟩
  invFun b := (b.alice, RawProtocol.matched b.alice b.bob)
  left_inv p := by simp only [matched_bob]
  right_inv b := by
    rcases b with ⟨alice,bob⟩
    change BB84RandomSource.Bases.mk alice (bobBases alice (RawProtocol.matched alice bob)) =
      BB84RandomSource.Bases.mk alice bob
    congr 1
    funext i
    cases ha : alice i <;> cases hb : bob i <;>
      simp [bobBases, RawProtocol.matched, ha, hb, opposite]

def testDistribution {n : Nat} (M : Finset (Fin n)) (k : Nat) : PMF (Finset (Fin n)) :=
  if hk : k ≤ M.card then Sampling.sample M k hk else PMF.pure ∅

def requiredLength {n : Nat} (M : Finset (Fin n)) (k minKey : Nat) : Nat :=
  if k ≤ M.card then minKey else M.card + 1

theorem test_eq {n : Nat} (θ : Fin n → BB84Basis) (M : Finset (Fin n)) (k : Nat) :
    Randomized.testDistribution ((basisEquiv n (θ,M)).seed) k = testDistribution M k := by
  change Randomized.testDistribution ⟨θ,bobBases θ M,fun _ => 0⟩ k = _
  simp only [Randomized.testDistribution, matched_bob, testDistribution]

theorem length_eq {n : Nat} (θ : Fin n → BB84Basis) (M : Finset (Fin n)) (k minKey : Nat) :
    Randomized.requiredLength ((basisEquiv n (θ,M)).seed) k minKey = requiredLength M k minKey := by
  change Randomized.requiredLength ⟨θ,bobBases θ M,fun _ => 0⟩ k minKey = _
  simp only [Randomized.requiredLength, matched_bob, requiredLength]

/-- Sample the public match set first and the independent bases second.
The source in each branch still includes the actual arbitrary block attack. -/
def record {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Density (BB84RawSource.outputSpace n e) :=
  Density.mixture (Foundation.Probability.uniform (Finset (Fin n))) (fun M =>
    Density.mixture (Foundation.Probability.uniform (Fin n → BB84Basis)) (fun θ =>
      Density.mixture (testDistribution M k) (fun T =>
        BB84RawSource.state A θ (bobBases θ M) T (requiredLength M k minKey) tolerance)))

theorem source_record_eq {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    (record A k minKey tolerance).matrix = (BB84RandomSource.record A k minKey tolerance).matrix := by
  unfold BB84RandomSource.record
  rw [← Density.mixture_uniform_equiv (basisEquiv n), Density.mixture_uniform_product]
  simp only [test_eq, length_eq]
  exact Density.mixture_commute _ _ _

/-- The reparametrized source experiment is the original randomized
prepare/attack experiment, by its already interpreted finite derivation. -/
theorem record_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (record A k minKey tolerance).matrix = (Randomized.record A k minKey tolerance).matrix :=
  (source_record_eq A k minKey tolerance).trans (BB84RandomSource.record_eq A k minKey tolerance)

theorem keyState_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
      (record A k minKey tolerance)).matrix = (Randomized.keyState A k minKey tolerance).matrix :=
  congrArg (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).toKraus.apply
    (record_eq A k minKey tolerance)

theorem publicState_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    ((RawProtocol.publicChannel n e).run (record A k minKey tolerance)).matrix =
      (Randomized.publicState A k minKey tolerance).matrix :=
  congrArg (RawProtocol.publicChannel n e).toKraus.apply (record_eq A k minKey tolerance)

end
end Foundation.Quantum.QKD.BB84SiftingRandomness
