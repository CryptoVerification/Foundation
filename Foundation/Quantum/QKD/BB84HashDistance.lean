import Foundation.Quantum.QKD.DominatedLeak
import Foundation.Quantum.QKD.BB84Collision

/-! Public-seed distance bounds on the actual accepted BB84 input. The old
public transcript and Eve remain quantum side information. The inverse-root
reconstruction and the phase-error input bound are still proof obligations. -/
namespace Foundation.Quantum.QKD.Collision
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

/-- The hashed operator is precisely the earlier physical relabeling of the
accepted state, not an unrelated probability distribution. -/
theorem accepted_hashed_operator {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) (seed : Hashing.RawSeed n length) :
    hashed (acceptedInput A k minKey tolerance).block (Hashing.rawHash seed) =
      Subnormalized.joint (Subnormalized.relabel (acceptedInput A k minKey tolerance) (Hashing.rawHash seed)) := by
  rw [← ClassicalBlocks.joint]
  rfl

/-- Publishing the seed keeps the original acceptance weight; no conditional
renormalization is used in the output operator. -/
theorem accepted_published_trace {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
      (fun seed => hashed (acceptedInput A k minKey tolerance).block (Hashing.rawHash seed))).trace =
        (Subnormalized.mass (acceptedInput A k minKey tolerance) : ℂ) := by
  let p := Foundation.Probability.uniform (Hashing.RawSeed n length)
  have ht (seed : Hashing.RawSeed n length) :
      (hashed (acceptedInput A k minKey tolerance).block (Hashing.rawHash seed)).trace =
        (Subnormalized.mass (acceptedInput A k minKey tolerance) : ℂ) := by
    rw [accepted_hashed_operator, Subnormalized.joint_trace_complex, Subnormalized.mass_relabel]
  rw [publicMixture_trace]
  simp_rw [ht]
  rw [← Finset.sum_mul]
  have hw : (∑ seed, ((p seed).toReal : ℂ)) = 1 := by exact_mod_cast Density.probability_weights p
  change (∑ seed, ((p seed).toReal : ℂ)) * _ = _
  rw [hw, one_mul]

theorem accepted_published_comparator_trace {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
      (fun _ => uniformComparator (Y := IdealKey.Key length) (acceptedInput A k minKey tolerance).block)).trace =
        (Subnormalized.mass (acceptedInput A k minKey tolerance) : ℂ) := by
  rw [← accepted_published_trace (length := length) A k minKey tolerance]
  rw [publicMixture_trace, publicMixture_trace]
  apply Finset.sum_congr rfl
  intro seed _
  rw [hashed_trace]

/-- All freshly sampled public matrix seeds, the hashed Alice key, every old
public value and the adversarial auxiliary system are observed jointly. -/
theorem accepted_published_distance {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat)
    (W D : Operator (Guessing.publicSpace (RawProtocol.PublicRecord n) e))
    (hrec : ∀ x, (acceptedInput A k minKey tolerance).block x =
      D.conjTranspose * sandwich W (acceptedInput A k minKey tolerance).block x * D) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun seed => hashed (acceptedInput A k minKey tolerance).block (Hashing.rawHash seed)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => uniformComparator (Y := IdealKey.Key length) (acceptedInput A k minKey tolerance).block))
      ((1/2:ℝ)*Real.sqrt ((Fintype.card (IdealKey.Key length) *
        ((D*D.conjTranspose)*(D*D.conjTranspose)).trace.re) *
          input (sandwich W (acceptedInput A k minKey tolerance).block))) := by
  apply published_two_universal _ _ _ (acceptedInput A k minKey tolerance).positive W D hrec
  intro x x' hx
  exact le_of_eq (raw_collision x x' hx)

/-- For every faithful finite reference state, the actual BB84 output has a
dimension-independent reconstruction cost. The input collision still has to
be bounded from protocol evidence before this yields a useful key length. -/
theorem accepted_faithful_distance {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat)
    (τ : Density (Guessing.publicSpace (RawProtocol.PublicRecord n) e)) (hτ : IsUnit τ.matrix) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun seed => hashed (acceptedInput A k minKey tolerance).block (Hashing.rawHash seed)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => uniformComparator (Y := IdealKey.Key length) (acceptedInput A k minKey tolerance).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        input (sandwich (quarterRoot τ.matrix)⁻¹ (acceptedInput A k minKey tolerance).block))) := by
  apply faithful_reference_distance _ _ _ (acceptedInput A k minKey tolerance).positive τ hτ
  intro x x' hx
  exact le_of_eq (raw_collision x x' hx)

/-- A proved operator domination on the actual accepted BB84 input yields a
public-seed observation error, with the original acceptance weight retained. -/
theorem accepted_dominated_distance {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat)
    (τ : Density (Guessing.publicSpace (RawProtocol.PublicRecord n) e)) (hτ : IsUnit τ.matrix)
    (q : ℝ) (hdom : Subnormalized.Dominated (acceptedInput A k minKey tolerance) τ q) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun seed => hashed (acceptedInput A k minKey tolerance).block (Hashing.rawHash seed)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => uniformComparator (Y := IdealKey.Key length) (acceptedInput A k minKey tolerance).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length)) *
          (q*Subnormalized.mass (acceptedInput A k minKey tolerance))))) := by
  apply dominated_published_distance _ _ _ τ hτ q hdom
  intro x x' hx
  exact le_of_eq (raw_collision x x' hx)

/-- The weight in the previous bound is exactly the existing physical
acceptance probability on the normalized full protocol output. -/
theorem accepted_input_mass {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    Subnormalized.mass (acceptedInput A k minKey tolerance) =
      (recordEvent e (fun t => (((Fintype.equivFin (RawProtocol.Output n)).symm t).transcript.accepted = true))).probability
        (Randomized.keyState A k minKey tolerance) := by
  unfold acceptedInput
  rw [Subnormalized.mass_withPublic, Accepted.mass_acceptance]

/-- The general finite derivation applies to the actual accepted BB84 state,
including singular reference states. Both premises are discharged explicitly. -/
theorem accepted_dominated_distance_general {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat)
    (τ : Density (Guessing.publicSpace (RawProtocol.PublicRecord n) e))
    (q : ℝ) (hq : 0 ≤ q) (hdom : Subnormalized.Dominated (acceptedInput A k minKey tolerance) τ q) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun seed => hashed (acceptedInput A k minKey tolerance).block (Hashing.rawHash seed)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => uniformComparator (Y := IdealKey.Key length) (acceptedInput A k minKey tolerance).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length)) *
          (q*Subnormalized.mass (acceptedInput A k minKey tolerance))))) := by
  apply PrivacyAmplificationLogic.sound _ Hashing.rawHash (fun _ => acceptedInput A k minKey tolerance)
    (fun _ => τ) (fun x x' hx => le_of_eq (raw_collision x x' hx))
    (PrivacyAmplificationLogic.proof (Fintype.card (IdealKey.Key length)) 0 0 q
      (Subnormalized.mass (acceptedInput A k minKey tolerance)) _ hq le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact hdom
  · have hi1 : i = 1 := by omega
    subst i
    exact le_rfl

/-- An additional publicly recorded deterministic message is accounted for
before hashing the accepted BB84 key. Active message tampering, authentication
and an error-correction decoder are separate protocol constructions. -/
theorem accepted_disclosed_privacy {n length : Nat} {e : Space} {C : Type}
    [Fintype C] [Nonempty C] [DecidableEq C] (A : BlockAttack n e) (k minKey tolerance : Nat)
    (message : RawGuess.Key n → RawProtocol.PublicRecord n → C)
    (τ : Density (Guessing.publicSpace (RawProtocol.PublicRecord n) e))
    (q : ℝ) (hq : 0 ≤ q) (hdom : Subnormalized.Dominated (acceptedInput A k minKey tolerance) τ q) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun seed => hashed (Subnormalized.withPublic (Subnormalized.withPublic
          (Subnormalized.disclose (Accepted.state A k minKey tolerance) message))).block (Hashing.rawHash seed)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => uniformComparator (Y := IdealKey.Key length) (Subnormalized.withPublic (Subnormalized.withPublic
          (Subnormalized.disclose (Accepted.state A k minKey tolerance) message))).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length)*
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card C*q)*Subnormalized.mass (Accepted.state A k minKey tolerance))))) := by
  apply Subnormalized.disclose_privacy _ message τ q hq hdom
  intro x x' hx
  exact le_of_eq (raw_collision x x' hx)

end
end Foundation.Quantum.QKD.Collision
