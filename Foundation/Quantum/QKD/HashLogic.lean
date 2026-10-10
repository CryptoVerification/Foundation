import Foundation.Quantum.QKD.BB84LinearHash
import Foundation.Logic.Presentation

/-! Finite collision-probability reasoning for the concrete binary matrix
family. Pair inputs are fixed before a fresh independent uniform seed; finite
mixtures choose the pair before sampling that seed. These rules do not assert
quantum secrecy or permit arbitrary semantic truths as nullary axioms. -/
namespace Foundation.Quantum.QKD.HashLogic
noncomputable section
open Foundation.Logic Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

inductive Experiment (n : Nat) where
  | pair : Finalization.RawKey n → Finalization.RawKey n → Experiment n
  | mixture (m : Nat) (p : PMF (Fin m)) (t : Fin m → Experiment n) : Experiment n

inductive Rule (n length : Nat) where
  | linear (r s : Finalization.RawKey n) (h : r ≠ s)
  | diagonal (r : Finalization.RawKey n)
  | mixture (m : Nat) (p : PMF (Fin m)) (t : Fin m → Experiment n) (ε : Fin m → ℝ)
  | weaken (t : Experiment n) (ε δ : ℝ) (h : ε ≤ δ)

abbrev presentation (n length : Nat) : Presentation where
  Judgment := Experiment n × ℝ
  Rule := Rule n length
  arity := fun | .linear .. | .diagonal .. => 0 | .mixture m .. => m | .weaken .. => 1
  premise := fun
    | .linear .. | .diagonal .. => Fin.elim0
    | .mixture _ _ t ε => fun i => (t i,ε i)
    | .weaken t ε _ _ => fun _ => (t,ε)
  conclusion := fun
    | .linear r s _ => (.pair r s, 1 / (2:ℝ)^length)
    | .diagonal r => (.pair r r,1)
    | .mixture m p t ε => (.mixture m p t,∑ i, (p i).toReal * ε i)
    | .weaken t _ δ _ => (t,δ)

def run {n : Nat} (length : Nat) : Experiment n → PMF Bool
  | .pair r s => (uniform (Hashing.RawSeed n length)).map (fun M => decide (Hashing.rawHash M r = Hashing.rawHash M s))
  | .mixture _ p t => p.bind (fun i => run length (t i))

def probability {n : Nat} (length : Nat) (t : Experiment n) : ℝ :=
  (eventProb (run length t) (fun b => b = true)).toReal

theorem pair_probability {n : Nat} (length : Nat) (r s : Finalization.RawKey n) :
    probability length (.pair r s) =
      (eventProb (uniform (Hashing.RawSeed n length)) (fun M => Hashing.rawHash M r = Hashing.rawHash M s)).toReal := by
  unfold probability run eventProb
  rw [PMF.toOuterMeasure_map_apply]
  congr 1
  congr 1
  ext M
  simp

theorem mixture_probability {n : Nat} (length m : Nat) (p : PMF (Fin m)) (t : Fin m → Experiment n) :
    probability length (.mixture m p t) = ∑ i, (p i).toReal * probability length (t i) :=
  eventProb_bind_toReal p (fun i => run length (t i)) _

def model (n length : Nat) : Model (presentation n length) where
  Carrier j := probability length j.1 ≤ j.2
  operation := fun r h => by
    cases r with
    | linear r s hrs => exact le_of_eq ((pair_probability length r s).trans (Hashing.raw_collision r s hrs))
    | diagonal r =>
      rw [pair_probability]
      simp [eventProb]
      have hm : ∑ x, (uniform (Hashing.RawSeed n length)) x = 1 := by
        simpa only [tsum_fintype] using (uniform (Hashing.RawSeed n length)).tsum_coe
      rw [hm]
      simp
    | mixture m p t ε =>
      rw [mixture_probability]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) ENNReal.toReal_nonneg)
    | weaken t ε δ hεδ => exact (h 0).trans hεδ

theorem sound (n length : Nat) {Γ : Logic.Context (presentation n length)} {j}
    (d : Derivation (presentation n length) Γ j)
    (h : ∀ i, (model n length).Carrier (Γ.claim i)) : (model n length).Carrier j := d.eval _ h

theorem interpretation_substitute (n length : Nat)
    {Γ Δ : Logic.Context (presentation n length)} {j} (d : Derivation (presentation n length) Γ j)
    (r : ∀ i, Derivation (presentation n length) Δ (Γ.claim i))
    (h : ∀ i, (model n length).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model n length) h =
      d.eval (model n length) (fun i => (r i).eval (model n length) h) :=
  Derivation.eval_substitute _ h d r

end
end Foundation.Quantum.QKD.HashLogic
