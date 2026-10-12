import Foundation.Quantum.QKD.UsefulBB84Availability

/-! A noiseless identity transmission, with the unit environment retained.
Matched positions are correct in every supported quantum measurement outcome;
mismatched positions are genuinely measured, not assigned Alice's bits. -/
namespace Foundation.Quantum.QKD.HonestBB84
noncomputable section
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

def appendUnit (a : Space) : Op a (.tensor a .unit) := fun i j => if i.1 = j then 1 else 0

theorem appendUnit_isometry (a : Space) : (appendUnit a).conjTranspose * appendUnit a = 1 := by
  ext i j
  simp [appendUnit, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, eq_comm]

def attack (n : Nat) : BlockAttack n .unit :=
  Channel.ofIsometry (appendUnit (qubits n)) (appendUnit_isometry _)

theorem discard_attack (n : Nat) (ρ : Density (qubits n)) :
    ((discardRight (qubits n) .unit).run ((attack n).run ρ)).matrix = ρ.matrix := by
  ext i j
  change (discardRight (qubits n) .unit).toKraus.apply _ i j = _
  rw [discardRight_apply]
  simp [attack, Channel.run, Channel.ofIsometry, Kraus.single_apply, appendUnit,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

def relativeGate (n : Nat) (alice bob : Fin n → BB84Basis) : Operator (qubits n) :=
  blockGate n bob * blockGate n alice

theorem relativeGate_succ (n : Nat) (alice bob : Fin (n+1) → BB84Basis) :
    relativeGate (n+1) alice bob = Op.tensor (bitGate (bob 0) * bitGate (alice 0))
      (relativeGate n (fun i => alice i.succ) (fun i => bob i.succ)) := by
  change Matrix.kronecker (bitGate (bob 0)) (blockGate n (fun i => bob i.succ)) *
    Matrix.kronecker (bitGate (alice 0)) (blockGate n (fun i => alice i.succ)) =
    Matrix.kronecker (bitGate (bob 0) * bitGate (alice 0))
      (blockGate n (fun i => bob i.succ) * blockGate n (fun i => alice i.succ))
  exact (Matrix.mul_kronecker_mul _ _ _ _).symm

theorem relativeGate_zero (n : Nat) (alice bob : Fin n → BB84Basis)
    (b : Fin n → Fin 2) (r : (qubits n).Basis) (i : Fin n)
    (hi : alice i = bob i) (hb : readBits r i ≠ b i) :
    relativeGate n alice bob r (writeBits n b) = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases r with ⟨r,s⟩
    rw [relativeGate_succ]
    revert hi hb
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi hb
      change (bitGate (bob 0) * bitGate (alice 0)) r (b 0) * _ = 0
      change r ≠ b 0 at hb
      have hg : bitGate (bob 0) * bitGate (alice 0) = 1 := by rw [hi, bitGate_square]
      rw [hg]
      simp [hb]
    · intro hi hb
      change (bitGate (bob 0) * bitGate (alice 0)) r (b 0) *
        relativeGate n (fun k => alice k.succ) (fun k => bob k.succ) s
          (writeBits n (fun k => b k.succ)) = 0
      have hz := ih (fun k => alice k.succ) (fun k => bob k.succ)
        (fun k => b k.succ) s j hi (by simpa [readBits] using hb)
      rw [hz, mul_zero]

theorem conjugate_basis_entry {a : Space} (U : Operator a) (x i j : a.Basis) :
    (U * (basisDensity a x).matrix * U.conjTranspose) i j = U i x * star (U j x) := by
  simp [basisDensity, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    ite_mul, mul_ite, eq_comm]

theorem decoded_entry (n : Nat) (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (r : (qubits n).Basis) :
    (((blockBasisChannel n bob).run (blockPrepare n alice b)).matrix r r) =
      relativeGate n alice bob r (writeBits n b) * star (relativeGate n alice bob r (writeBits n b)) := by
  simp only [blockPrepare, blockBasisChannel, Channel.run, Channel.ofIsometry, Kraus.single_apply]
  have he : blockGate n bob * (blockGate n alice * (basisDensity (qubits n) (writeBits n b)).matrix *
      (blockGate n alice).conjTranspose) * (blockGate n bob).conjTranspose =
      relativeGate n alice bob * (basisDensity (qubits n) (writeBits n b)).matrix *
        (relativeGate n alice bob).conjTranspose := by
    simp [relativeGate, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he, conjugate_basis_entry]

theorem supported_matched (n : Nat) (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (r : Fin (Fintype.card (qubits n).Basis)) (hr : r ∈ ((attack n).outcome alice bob b).support)
    (i : Fin n) (hi : alice i = bob i) : blockOutcomeBits n r i = b i := by
  by_contra hb
  have he := (attack n).outcome_event alice bob b r
  have hm : ((discardRight (qubits n) .unit).run ((attack n).jointState alice b)).matrix =
      (blockPrepare n alice b).matrix := discard_attack n _
  have hp : (blockMeasurement n bob).probability
      ((discardRight (qubits n) .unit).run ((attack n).jointState alice b)) r = 0 := by
    rw [blockMeasurement, Instrument.pre_probability, basisInstrument_probability,
      BB84Attack.basisEffect_probability]
    change (((blockBasisChannel n bob).toKraus.apply
      ((discardRight (qubits n) .unit).run ((attack n).jointState alice b)).matrix) _ _).re = 0
    rw [hm]
    change (((blockBasisChannel n bob).run (blockPrepare n alice b)).matrix _ _).re = 0
    rw [decoded_entry, relativeGate_zero n alice bob b _ i hi hb]
    simp
  rw [hp, ENNReal.ofReal_zero] at he
  have hz : ((attack n).outcome alice bob b) r = 0 := by
    simpa [eventProb, PMF.toOuterMeasure_apply_singleton] using he
  exact hr hz

theorem raw_output_eq {n : Nat} (alice bob : Fin n → BB84Basis) (b c : Fin n → Fin 2)
    (T : Finset (Fin n)) (minKey tolerance : Nat) (hT : T ⊆ RawProtocol.matched alice bob)
    (hc : ∀ i ∈ RawProtocol.matched alice bob, c i = b i) :
    RawProtocol.output alice bob b c T minKey tolerance =
      RawProtocol.output alice bob b b T minKey tolerance := by
  have herr : RawProtocol.errors b c T = 0 := by
    unfold RawProtocol.errors
    have he : T.filter (fun i => b i ≠ c i) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hi
      simp [hc i (hT hi)]
    rw [he, Finset.card_empty]
  have ha : RawProtocol.accepts alice bob b c T minKey tolerance =
      RawProtocol.accepts alice bob b b T minKey tolerance := by
    have hs : RawProtocol.errors b b T = 0 := by simp [RawProtocol.errors]
    simp only [RawProtocol.accepts, herr, hs]
  unfold RawProtocol.output
  simp only [ha]
  congr 1
  · congr 1
    funext i
    by_cases hi : i ∈ T
    · simp [hi, hc i (hT hi)]
    · simp [hi]
  · funext i
    split_ifs with hi
    · rw [hc i ((Finset.mem_sdiff.mp hi.2).1)]
    · rfl

private theorem bind_congr_support {X Y : Type*} (p : PMF X) (f g : X → PMF Y)
    (h : ∀ x ∈ p.support, f x = g x) : p.bind f = p.bind g := by
  ext y
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro x
  by_cases hx : p x = 0
  · simp [hx]
  · rw [h x hx]

theorem conditional_outcome {n : Nat} (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (T : Finset (Fin n)) (minKey tolerance : Nat) (hT : T ⊆ RawProtocol.matched alice bob) :
    (((attack n).outcome alice bob b).map (fun r =>
      RawProtocol.output alice bob b (blockOutcomeBits n r) T minKey tolerance)) =
      PMF.pure (RawProtocol.output alice bob b b T minKey tolerance) := by
  change (((attack n).outcome alice bob b).bind _) = _
  calc
    _ = ((attack n).outcome alice bob b).bind (fun _ =>
        PMF.pure (RawProtocol.output alice bob b b T minKey tolerance)) := by
      apply bind_congr_support
      intro r hr
      apply congrArg PMF.pure
      apply raw_output_eq _ _ _ _ _ _ _ hT
      intro i hi
      exact supported_matched n alice bob b r hr i (by simpa [RawProtocol.matched] using hi)
    _ = _ := PMF.bind_const _ _

def seedEquiv (n : Nat) :
    (((Fin n → BB84Basis) × (Fin n → Fin 2)) × Finset (Fin n)) ≃ Randomized.Seed n where
  toFun p := ⟨p.1.1, BB84SiftingRandomness.bobBases p.1.1 p.2, p.1.2⟩
  invFun s := ((s.alice,s.bits), RawProtocol.matched s.alice s.bob)
  left_inv p := by simp [BB84SiftingRandomness.matched_bob]
  right_inv s := by
    have h := (BB84SiftingRandomness.basisEquiv n).right_inv ⟨s.alice,s.bob⟩
    have hb := congrArg BB84RandomSource.Bases.bob h
    simp only [BB84SiftingRandomness.basisEquiv] at hb
    cases s
    simp_all

def records (n k minKey : Nat) (θ : Fin n → BB84Basis) (b : Fin n → Fin 2) :=
  (uniform (Finset (Fin n))).bind (fun M =>
    (BB84SiftingRandomness.testDistribution M k).map (fun T =>
      RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T
        (BB84SiftingRandomness.requiredLength M k minKey) 0))

/-- Exact classical output law of the physical independent-basis experiment.
Unmatched measurement outcomes disappear only through the raw-output map. -/
theorem outcome_eq_records (n k minKey : Nat) :
    Randomized.outcome (attack n) k minKey 0 =
      (uniform ((Fin n → BB84Basis) × (Fin n → Fin 2))).bind
        (fun p => records n k minKey p.1 p.2) := by
  classical
  unfold Randomized.outcome Randomized.configurationDistribution
  rw [PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  unfold Randomized.seedDistribution
  rw [← uniform_map_equiv (seedEquiv n), PMF.bind_map]
  rw [← uniform_pair, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  apply congrArg (PMF.bind _)
  funext p
  unfold records
  apply congrArg (PMF.bind _)
  funext M
  change (Randomized.testDistribution
    (⟨p.1, BB84SiftingRandomness.bobBases p.1 M, p.2⟩ : Randomized.Seed n) k).bind
      (fun T => ((attack n).outcome p.1 (BB84SiftingRandomness.bobBases p.1 M) p.2).map
        (fun r => RawProtocol.output p.1 (BB84SiftingRandomness.bobBases p.1 M) p.2
          (blockOutcomeBits n r) T
          (Randomized.requiredLength ⟨p.1, BB84SiftingRandomness.bobBases p.1 M, p.2⟩ k minKey) 0)) = _
  simp only [Randomized.testDistribution, Randomized.requiredLength, BB84SiftingRandomness.matched_bob]
  change (BB84SiftingRandomness.testDistribution M k).bind _ =
    (BB84SiftingRandomness.testDistribution M k).bind _
  apply bind_congr_support
  intro T hT
  have ht : T ⊆ M := by
    by_cases hk : k ≤ M.card
    · rw [BB84SiftingRandomness.testDistribution, dif_pos hk] at hT
      simp only [Sampling.sample, PMF.mem_support_uniformOfFinset_iff] at hT
      exact (Finset.mem_powersetCard.mp hT).1
    · rw [BB84SiftingRandomness.testDistribution, dif_neg hk] at hT
      have he := (PMF.mem_support_pure_iff _ _).mp hT
      subst T
      exact Finset.empty_subset _
  exact conditional_outcome _ _ _ T _ _ (by rwa [BB84SiftingRandomness.matched_bob])

theorem outcome_eq_errorFreeRecords :
    Randomized.outcome (attack UsefulBB84.signals) UsefulBB84.tests UsefulBB84.minKey 0 =
      (uniform ((Fin UsefulBB84.signals → BB84Basis) × (Fin UsefulBB84.signals → Fin 2))).bind
        (fun p => UsefulBB84.errorFreeRecords p.1 p.2) :=
  outcome_eq_records _ _ _

end
end Foundation.Quantum.QKD.HonestBB84
