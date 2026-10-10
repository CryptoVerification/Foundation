import Foundation.Quantum.QKD.BB84PairwiseSelection
import Foundation.Logic.Presentation

/-! A finite object logic for the fixed-reference measurement correspondence,
its random mixtures, and physical later processing. These inference rules are
our reconstruction, not a claimed verbatim calculus from Bouman--Fehr. -/
namespace Foundation.Quantum.QKD.BB84PairwiseLogic
noncomputable section
open Foundation.Logic BB84DelayedMeasurements BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

inductive Claim (n : Nat) where
  | first (θ : Fin n → BB84Basis)
  | mixed (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m))
  | processed (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m)) (c : Nat)

inductive Rule (n : Nat) where
  | first (θ : Fin n → BB84Basis)
  | mix (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m))
  | post (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m)) (c : Nat)

abbrev presentation (n : Nat) : Presentation where
  Judgment := Claim n
  Rule := Rule n
  arity := fun | .first _ => 0 | .mix m .. => m | .post .. => 1
  premise := fun
    | .first _ => Fin.elim0
    | .mix _ θ _ => fun i => .first (θ i)
    | .post m θ p _ => fun _ => .mixed m θ p
  conclusion := fun
    | .first θ => .first θ
    | .mix m θ p => .mixed m θ p
    | .post m θ p c => .processed m θ p c

abbrev recordSpace (n : Nat) (e : Space) := Space.tensor (.register (count n)) (jointSpace n e)

variable {n : Nat} {e b : Space}

def model (ρ : Density (jointSpace n e)) (C : Nat → Channel (recordSpace n e) b) :
    Model (presentation n) where
  Carrier := fun
    | .first θ => ((actualFirst θ e).record.run ρ).matrix = ((referenceFirst θ e).record.run ρ).matrix
    | .mixed _ θ p =>
        (Density.mixture p (fun i => (actualFirst (θ i) e).record.run ρ)).matrix =
          (Density.mixture p (fun i => (referenceFirst (θ i) e).record.run ρ)).matrix
    | .processed _ θ p c =>
        ((C c).run (Density.mixture p (fun i => (actualFirst (θ i) e).record.run ρ))).matrix =
          ((C c).run (Density.mixture p (fun i => (referenceFirst (θ i) e).record.run ρ))).matrix
  operation := fun r hs => by
    cases r with
    | first θ => exact actual_reference θ e ρ.matrix
    | mix _ _ p => exact Density.mixture_congr_matrix p _ _ hs
    | post _ _ _ c => exact congrArg (C c).toKraus.apply (hs 0)

theorem sound (ρ : Density (jointSpace n e)) (C : Nat → Channel (recordSpace n e) b)
    {Γ : Context (presentation n)} {j} (d : Derivation (presentation n) Γ j)
    (hs : ∀ i, (model ρ C).Carrier (Γ.claim i)) : (model ρ C).Carrier j := d.eval _ hs

theorem interpretation_substitute (ρ : Density (jointSpace n e))
    (C : Nat → Channel (recordSpace n e) b)
    {Γ Δ : Context (presentation n)} {j} (d : Derivation (presentation n) Γ j)
    (f : ∀ i, Derivation (presentation n) Δ (Γ.claim i))
    (hs : ∀ i, (model ρ C).Carrier (Δ.claim i)) :
    (d.substitute f).eval (model ρ C) hs =
      d.eval (model ρ C) (fun i => (f i).eval (model ρ C) hs) :=
  Derivation.eval_substitute _ hs d f

def firstProof (θ : Fin n → BB84Basis) :
    Derivation (presentation n) (.empty _) (.first θ) :=
  .apply (T := presentation n) (.first θ) (fun i => Fin.elim0 i)

def proof (m : Nat) (θ : Fin m → Fin n → BB84Basis) (p : PMF (Fin m)) (c : Nat) :
    Derivation (presentation n) (.empty _) (.processed m θ p c) := by
  apply Derivation.apply (T := presentation n) (.post m θ p c)
  intro _
  apply Derivation.apply (T := presentation n) (.mix m θ p)
  intro i
  exact firstProof (θ i)

end
end Foundation.Quantum.QKD.BB84PairwiseLogic
