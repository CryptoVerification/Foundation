import Foundation.Crypto.Logic.Polygraph.FiniteMaximalStep

/-! Transport maximal conditional kernels through a decodable state encoding.
The encoded state type need not be finite. Only its reachable law is the
image of a finite law. Unreachable states use the explicitly supplied decoder. -/
namespace CryptoLogic.Polygraph.Experiment.EncodedMaximal
open Foundation.Probability
open GameCoherence
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {α β : Type} [Fintype α]
variable (encode : α → β) (decode : β → α) (inverse : Function.LeftInverse decode encode)

abbrev game (p : PMF α) (event : β → Prop) : Observed := ⟨β, .sample (p.map encode), event⟩

def kernel (p q : PMF α) (state : β) : PMF β :=
  (FiniteMaximalCoupling.kernel p q (decode state)).map encode

include inverse in
theorem preserve (p q : PMF α) : (p.map encode).bind (kernel encode decode p q) = q.map encode := by
  have hi (x : α) : decode (encode x) = x := inverse x
  rw [PMF.bind_map]
  simp only [Function.comp_def, kernel, hi]
  rw [← PMF.map_bind, FiniteMaximalCoupling.kernel_preserve]

include inverse in
theorem joint_eq (p q : PMF α) :
    ((p.map encode).bind fun x => (kernel encode decode p q x).map fun y => (x,y)) =
      (FiniteMaximalCoupling.joint p q).map (fun pair => (encode pair.1, encode pair.2)) := by
  have hi (x : α) : decode (encode x) = x := inverse x
  rw [← FiniteMaximalCoupling.kernel_joint, PMF.map_bind, PMF.bind_map]
  simp only [kernel, PMF.map_comp, Function.comp_def, hi]

include inverse in
theorem mismatch_probability (p q : PMF α) :
    eventProb ((FiniteMaximalCoupling.joint p q).map (fun pair => (encode pair.1, encode pair.2)))
      (fun pair => pair.1 ≠ pair.2) = ENNReal.ofReal (finiteVariation p q) := by
  rw [eventProb_map]
  have h : (fun pair : α × α => encode pair.1 ≠ encode pair.2) = (fun pair => pair.1 ≠ pair.2) := by
    funext pair
    exact propext (not_congr (inverse.injective.eq_iff))
  rw [h, FiniteMaximalCoupling.mismatch_probability]

def step (p q : PMF α) (event : β → Prop) : Step (game encode p event) (game encode q event) where
  kernel := kernel encode decode p q
  preserve := preserve encode decode inverse p q
  bad pair := pair.1 ≠ pair.2
  agree x _ y _ good := by
    have same : x = y := not_ne_iff.mp good
    subst y
    rfl
  loss := ENNReal.ofReal (finiteVariation p q)
  bound := by
    change eventProb ((p.map encode).bind fun x => (kernel encode decode p q x).map fun y => (x,y)) _ ≤ _
    rw [joint_eq encode decode inverse, mismatch_probability encode decode inverse]

def toFinite (p : PMF α) (event : β → Prop) :
    Step (game encode p event) (FiniteMaximal.game p (fun x => event (encode x))) :=
  Step.ofMap _ _ decode (by
    change (p.map encode).map decode = p
    rw [PMF.map_comp]
    have h : decode ∘ encode = id := funext inverse
    rw [h, PMF.map_id]) (by
      intro state supported
      obtain ⟨x, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      rw [inverse])

def fromFinite (q : PMF α) (event : β → Prop) :
    Step (FiniteMaximal.game q (fun x => event (encode x))) (game encode q event) :=
  Step.ofMap _ _ encode rfl (fun _ _ => Iff.rfl)

def direct (p q : PMF α) (event : β → Prop) : Path (game encode p event) (game encode q event) :=
  .step (step encode decode inverse p q event)

def factored (p q : PMF α) (event : β → Prop) : Path (game encode p event) (game encode q event) :=
  .seq (.step (toFinite encode decode inverse p event))
    (.seq (.step (FiniteMaximal.step p q (fun x => event (encode x)))) (.step (fromFinite encode q event)))

theorem factorization_kernel (p q : PMF α) (event : β → Prop) (state : β) :
    (direct encode decode inverse p q event).kernel state =
      (factored encode decode inverse p q event).kernel state := by
  simp only [direct, factored, Path.kernel, step, toFinite, fromFinite, Step.ofMap,
    PMF.pure_bind, FiniteMaximal.step, kernel]
  rfl

theorem factorization_loss (p q : PMF α) (event : β → Prop) :
    (direct encode decode inverse p q event).loss = (factored encode decode inverse p q event).loss := by
  change ENNReal.ofReal (finiteVariation p q) = 0 + (ENNReal.ofReal (finiteVariation p q) + 0)
  simp

def factorizationCell (p q : PMF α) (event : β → Prop) :
    Cell4 (direct encode decode inverse p q event) (factored encode decode inverse p q event) :=
  .generator ⟨factorization_kernel encode decode inverse p q event, factorization_loss encode decode inverse p q event⟩

end
end CryptoLogic.Polygraph.Experiment.EncodedMaximal
