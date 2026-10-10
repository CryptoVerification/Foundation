import Foundation.Quantum.QKD.PairwiseQuantumSampling
import Foundation.Quantum.QKD.BB84PurifiedSource
import Foundation.Quantum.QKD.BB84SiftedInput

/-! Pairwise quantum sampling of the actual finite-Kraus attacked source,
purified and selected without any basis/test dependence. The extra Kraus
register and unmatched signals are retained as quantum auxiliary information. -/
namespace Foundation.Quantum.QKD.PairwiseAttackSampling
noncomputable section
open PureProjection BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

abbrev environment {n : Nat} {e : Space} (A : BlockAttack n e) :=
  Space.tensor e (.register (Fintype.card A.index))

def transport {n : Nat} {e : Space} (A : BlockAttack n e) :
    (BB84PurifiedSource.jointSpace A).Basis ≃
      (BB84DelayedMeasurements.jointSpace n (environment A)).Basis where
  toFun p := ((p.1.1.1,p.2),(p.1.1.2,p.1.2))
  invFun p := (((p.1.1,p.2.1),p.2.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def transported {n : Nat} {e : Space} (A : BlockAttack n e) :=
  (BasisChannel.channel (transport A)).run (BB84PurifiedSource.state A)

def selected {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :=
  (BasisChannel.channel (BB84SiftedInput.jointEquiv M (environment A))).run (transported A)

def state {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :=
  referenceInput (selected A M)

def vector {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :
    (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M)
      (BB84SiftedInput.auxiliary M (environment A))).Basis → ℂ :=
  (Op.tensor (referenceGate (BB84SiftedInput.selectedCount M))
    (Op.ident (BB84SiftedInput.auxiliary M (environment A)))).mulVec
      ((Op.tensor (Op.basisMap (BB84ErrorTransform.cnotEquiv (BB84SiftedInput.selectedCount M)))
        (Op.ident (BB84SiftedInput.auxiliary M (environment A)))).mulVec
          ((Op.basisMap (BB84SiftedInput.jointEquiv M (environment A))).mulVec
            ((Op.basisMap (transport A)).mulVec (BB84PurifiedSource.vector A))))

theorem pure {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :
    (state A M).matrix = rank (vector A M) (vector A M) := by
  have ht : (transported A).matrix =
      rank ((Op.basisMap (transport A)).mulVec (BB84PurifiedSource.vector A))
        ((Op.basisMap (transport A)).mulVec (BB84PurifiedSource.vector A)) := by
    change (Kraus.single (Op.basisMap (transport A))).apply (BB84PurifiedSource.state A).matrix = _
    rw [BB84PurifiedSource.pure, Kraus.single_apply, SourceReplacement.rank_conjugate]
  have hs : (selected A M).matrix =
      rank ((Op.basisMap (BB84SiftedInput.jointEquiv M (environment A))).mulVec
          ((Op.basisMap (transport A)).mulVec (BB84PurifiedSource.vector A)))
        ((Op.basisMap (BB84SiftedInput.jointEquiv M (environment A))).mulVec
          ((Op.basisMap (transport A)).mulVec (BB84PurifiedSource.vector A))) := by
    change (Kraus.single (Op.basisMap (BB84SiftedInput.jointEquiv M (environment A)))).apply
      (transported A).matrix = _
    rw [ht, Kraus.single_apply, SourceReplacement.rank_conjugate]
  change (Kraus.single (Op.tensor (referenceGate (BB84SiftedInput.selectedCount M))
    (Op.ident (BB84SiftedInput.auxiliary M (environment A))))).apply
      ((Kraus.single (Op.tensor (Op.basisMap (BB84ErrorTransform.cnotEquiv (BB84SiftedInput.selectedCount M)))
        (Op.ident (BB84SiftedInput.auxiliary M (environment A))))).apply (selected A M).matrix) = _
  rw [hs]
  rw [Kraus.single_apply, Kraus.single_apply]
  rw [SourceReplacement.rank_conjugate
    (a := BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M)
      (BB84SiftedInput.auxiliary M (environment A)))
    (b := BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M)
      (BB84SiftedInput.auxiliary M (environment A)))
    (Op.tensor (Op.basisMap (BB84ErrorTransform.cnotEquiv (BB84SiftedInput.selectedCount M)))
      (Op.ident (BB84SiftedInput.auxiliary M (environment A))))]
  rw [SourceReplacement.rank_conjugate
    (a := BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M)
      (BB84SiftedInput.auxiliary M (environment A)))
    (b := BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M)
      (BB84SiftedInput.auxiliary M (environment A)))
    (Op.tensor (referenceGate (BB84SiftedInput.selectedCount M))
      (Op.ident (BB84SiftedInput.auxiliary M (environment A))))]
  rfl

theorem unit {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :
    bracket (vector A M) (vector A M) = 1 := by
  have h := (state A M).normalized
  rw [pure, rank_trace] at h
  exact h

/-- An explicit normalized ideal joint state, with public selector and test set,
is within the proved square-root finite-count error of the real source. -/
theorem approximation {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    OperatorApprox
      (QuantumSampling.real (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk) (vector A M))
      (QuantumSampling.ideal (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
        (PairwiseQuantumSampling.good k gap) (vector A M)
          (fun _ => PairwiseQuantumSampling.fallback (vector A M) (unit A M)))
      (Real.sqrt (PairwiseSampling.errorBound (BB84SiftedInput.selectedCount M) k gap).toReal) :=
  PairwiseQuantumSampling.approximation (vector A M) (unit A M) k gap hk

end
end Foundation.Quantum.QKD.PairwiseAttackSampling
