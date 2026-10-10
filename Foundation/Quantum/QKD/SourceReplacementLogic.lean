import Foundation.Quantum.QKD.BB84SourceReplacement
import Foundation.Logic.Presentation

/-! Independently designed finite equations for source replacement, random
basis mixtures and subsequent physical processing. The source rule is the
proved full-state equality, not an arbitrary semantic truth constructor. -/
namespace Foundation.Quantum.QKD.SourceReplacementLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Term where
  | entangled (basis : Nat)
  | prepared (basis : Nat)
  | process (c : Nat) (t : Term)
  | mixture (n : Nat) (p : PMF (Fin n)) (t : Fin n → Term)

inductive Rule where
  | source (basis : Nat)
  | refl (t : Term)
  | symm (t u : Term)
  | trans (t u v : Term)
  | post (c : Nat) (t u : Term)
  | mixture (n : Nat) (p : PMF (Fin n)) (t u : Fin n → Term)

abbrev presentation : Presentation where
  Judgment := Term × Term
  Rule := Rule
  arity := fun | .source .. | .refl .. => 0 | .trans .. => 2 | .mixture n .. => n | _ => 1
  premise := fun
    | .source _ | .refl _ => Fin.elim0
    | .symm t u | .post _ t u => fun _ => (t,u)
    | .trans t u v => fun i => if i = 0 then (t,u) else (u,v)
    | .mixture _ _ t u => fun i => (t i,u i)
  conclusion := fun
    | .source θ => (.entangled θ,.prepared θ)
    | .refl t => (t,t)
    | .symm t u => (u,t)
    | .trans t _ v => (t,v)
    | .post c t u => (.process c t,.process c u)
    | .mixture n p t u => (.mixture n p t,.mixture n p u)

variable {n : Nat} {e : Space}
abbrev recordSpace (n : Nat) (e : Space) :=
  Space.tensor (.register (Fintype.card (qubits n).Basis)) (.tensor (qubits n) e)

def Term.eval (A : BlockAttack n e) (basis : Nat → Fin n → BB84Basis)
    (C : Nat → Channel (recordSpace n e) (recordSpace n e)) : Term → Density (recordSpace n e)
  | .entangled θ => BB84Source.record A (basis θ)
  | .prepared θ => BB84Source.ensemble A (basis θ)
  | .process c t => (C c).run (t.eval A basis C)
  | .mixture _ p t => Density.mixture p (fun i => (t i).eval A basis C)

def model (A : BlockAttack n e) (basis : Nat → Fin n → BB84Basis)
    (C : Nat → Channel (recordSpace n e) (recordSpace n e)) : Model presentation where
  Carrier j := (j.1.eval A basis C).matrix = (j.2.eval A basis C).matrix
  operation := fun r hs => by
    cases r with
    | source θ => exact BB84Source.uniform_replacement A (basis θ)
    | refl t => rfl
    | symm t u => exact (hs 0).symm
    | trans t u v => exact (hs 0).trans (hs 1)
    | post c t u => exact congrArg (C c).toKraus.apply (hs 0)
    | mixture m p t u =>
      change (∑ i, ((p i).toReal:ℂ) • ((t i).eval A basis C).matrix) = _
      apply Finset.sum_congr rfl
      intro i _
      rw [hs i]

theorem sound (A : BlockAttack n e) (basis : Nat → Fin n → BB84Basis)
    (C : Nat → Channel (recordSpace n e) (recordSpace n e))
    {Γ : Context presentation} {j} (d : Derivation presentation Γ j)
    (hs : ∀ i, (model A basis C).Carrier (Γ.claim i)) :
    (model A basis C).Carrier j := d.eval _ hs

theorem interpretation_substitute (A : BlockAttack n e) (basis : Nat → Fin n → BB84Basis)
    (C : Nat → Channel (recordSpace n e) (recordSpace n e))
    {Γ Δ : Context presentation} {j} (d : Derivation presentation Γ j)
    (f : ∀ i, Derivation presentation Δ (Γ.claim i))
    (hs : ∀ i, (model A basis C).Carrier (Δ.claim i)) :
    (d.substitute f).eval (model A basis C) hs =
      d.eval (model A basis C) (fun i => (f i).eval (model A basis C) hs) :=
  Derivation.eval_substitute _ hs d f

/-- A closed proof: replace each source, combine random bases, then process. -/
def proof (m c : Nat) (p : PMF (Fin m)) (basis : Fin m → Nat) :
    Derivation presentation (.empty _) (.process c (.mixture m p (fun i => .entangled (basis i))),
      .process c (.mixture m p (fun i => .prepared (basis i)))) := by
  apply Derivation.apply (T := presentation) (.post c _ _)
  intro _
  apply Derivation.apply (T := presentation) (.mixture m p _ _)
  intro i
  exact .apply (T := presentation) (.source (basis i)) (fun j => Fin.elim0 j)

end
end Foundation.Quantum.QKD.SourceReplacementLogic
