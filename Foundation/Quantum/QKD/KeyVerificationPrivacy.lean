import Foundation.Quantum.QKD.KeyVerification
import Foundation.Quantum.QKD.SubnormalizedOrder
import Foundation.Quantum.PublicMixtureObservation

/-! Public-tag leakage on the actual passing event. The seed is fixed in this
lemma and the bound is uniform over seeds; no seed-cardinality loss is charged.
All bounds apply to subnormalized states, without postselection division. -/
namespace Foundation.Quantum.QKD.KeyVerification
noncomputable section
open Subnormalized
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {K T S V : Type} [Fintype K] [Fintype T] [Fintype S] [Fintype V]
  [DecidableEq K] [DecidableEq T] [DecidableEq V] [Nonempty V] {e : Space}

def selected (ρ : State (Input K T) e) (hash : S → K → V) (s : S) :=
  restrict ρ (fun x => hash s x.1.1 = hash s x.1.2)

def fixedInput (ρ : State (Input K T) e) (hash : S → K → V) (s : S) :=
  withPublic (withPublic (disclose (CommonKey.aliceView (selected ρ hash s))
    (fun a _ => hash s a)))

omit [Fintype S] [Fintype V] [Nonempty V] in
/-- Passing is allowed to depend on both keys and hence on correlated quantum
information. Positivity, not independence of Bob or Eve, proves this step. -/
theorem selected_alice_dominated (ρ : State (Input K T) e) (hash : S → K → V) (s : S)
    (τ : Density (Guessing.publicSpace T e)) (q : ℝ)
    (hd : Dominated (withPublic (CommonKey.aliceView ρ)) τ q) :
    Dominated (withPublic (CommonKey.aliceView (selected ρ hash s))) τ q := by
  apply dominated_of_below _ _ τ q _ hd
  apply withPublic_below
  exact relabel_below _ _ _ (restrict_below ρ _)

omit [Fintype S] in
/-- Only the tag alphabet costs entropy; the estimate holds for every fixed
verification seed, before averaging its actual independent distribution. -/
theorem fixed_dominated (ρ : State (Input K T) e) (hash : S → K → V) (s : S)
    (τ : Density (Guessing.publicSpace T e)) (q : ℝ)
    (hd : Dominated (withPublic (CommonKey.aliceView ρ)) τ q) :
    Dominated (fixedInput ρ hash s) (leakedReference (C := V) τ) (Fintype.card V*q) :=
  disclose_dominated _ _ τ q (selected_alice_dominated ρ hash s τ q hd)

omit [Fintype S] in
/-- The existing PA derivation is interpreted after both the real check and
the tag disclosure. The hashing seed here is a *second*, independent seed. -/
theorem fixed_privacy {Y H : Type} [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype H]
    (ρ : State (Input K T) e) (hash : S → K → V) (s : S)
    (τ : Density (Guessing.publicSpace T e)) (q : ℝ) (hq : 0 ≤ q)
    (hd : Dominated (withPublic (CommonKey.aliceView ρ)) τ q)
    (p : PMF H) (f : H → K → Y)
    (hc : ∀ a b, a ≠ b → Collision.collision p f a b ≤ 1/Fintype.card Y) :
    (PrivacyAmplificationLogic.model p f (fun _ => fixedInput ρ hash s)
      (fun _ => leakedReference (C := V) τ) hc).Carrier
      (.distance 0 ((1/2:ℝ)*Real.sqrt (Fintype.card Y *
        ((1-1/Fintype.card Y)*((Fintype.card V*q)*1))))) := by
  apply PrivacyAmplificationLogic.sound p f _ _ hc
    (PrivacyAmplificationLogic.proof (Fintype.card Y) 0 0 (Fintype.card V*q) 1 _
      (mul_nonneg (Nat.cast_nonneg _) hq) le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact fixed_dominated ρ hash s τ q hd
  · have hi1 : i = 1 := by omega
    subst i
    exact (fixedInput ρ hash s).bounded

/-- Verification randomness remains an explicit public register on both
sides. Its possibly huge alphabet does not multiply the leakage coefficient. -/
theorem averaged_privacy {Y H : Type} [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype H]
    (ρ : State (Input K T) e) (hash : S → K → V) (verificationSeeds : PMF S)
    (τ : Density (Guessing.publicSpace T e)) (q : ℝ) (hq : 0 ≤ q)
    (hd : Dominated (withPublic (CommonKey.aliceView ρ)) τ q)
    (p : PMF H) (f : H → K → Y)
    (hc : ∀ a b, a ≠ b → Collision.collision p f a b ≤ 1/Fintype.card Y) :
    OperatorApprox
      (publicMixture verificationSeeds (fun s => publicMixture p
        (fun r => Collision.hashed (fixedInput ρ hash s).block (f r))))
      (publicMixture verificationSeeds (fun s => publicMixture p
        (fun _ => Collision.uniformComparator (Y := Y) (fixedInput ρ hash s).block)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card Y *
        ((1-1/Fintype.card Y)*((Fintype.card V*q)*1)))) := by
  have h := publicMixture_approx verificationSeeds _ _
    (fun _ => (1/2:ℝ)*Real.sqrt (Fintype.card Y *
      ((1-1/Fintype.card Y)*((Fintype.card V*q)*1))))
    (fun s => fixed_privacy ρ hash s τ q hq hd p f hc)
  simpa only [← Finset.sum_mul, Density.probability_weights, one_mul] using h

omit [Fintype S] [Nonempty V] in
/-- The actual selected Alice key and tag, with the old public register. -/
theorem fixedInput_label (ρ : State (Input K T) e) (hash : S → K → V) (s : S) :
    fixedInput ρ hash s = withPublic (withPublic
      (relabel (selected ρ hash s) (fun x => ((x.1.1,hash s x.1.1),x.2)))) := by
  unfold fixedInput disclose CommonKey.aliceView
  rw [relabel_comp]
  rfl

end
end Foundation.Quantum.QKD.KeyVerification
