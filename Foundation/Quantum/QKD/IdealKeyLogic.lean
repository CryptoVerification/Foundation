import Foundation.Logic.Presentation
import Foundation.Quantum.QKD.IdealKey

/-! Finite error reasoning for the explicit ideal-key construction. Only
specified proven operations are admitted; security of a real state is not a
nullary rule. This calculus is our independent reconstruction. -/
namespace Foundation.Quantum.QKD.IdealKeyLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Term where
  | state : Nat → Term
  | ideal : Term → Term

structure Claim where
  left : Term
  right : Term
  error : ℝ

inductive Rule where
  | refl (t : Term)
  | symm (t u : Term) (ε : ℝ)
  | trans (t u v : Term) (ε δ : ℝ)
  | ideal (t u : Term) (ε : ℝ)
  | fixed (t : Term)

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .refl .. | .fixed .. => 0 | .trans .. => 2 | _ => 1
  premise := fun
    | .refl .. | .fixed .. => Fin.elim0
    | .symm t u ε | .ideal t u ε => fun _ => ⟨t,u,ε⟩
    | .trans t u v ε δ => fun i => if i = 0 then ⟨t,u,ε⟩ else ⟨u,v,δ⟩
  conclusion := fun
    | .refl t => ⟨t,t,0⟩
    | .symm t u ε => ⟨u,t,ε⟩
    | .trans t _ v ε δ => ⟨t,v,ε+δ⟩
    | .ideal t u ε => ⟨.ideal t,.ideal u,ε⟩
    | .fixed t => ⟨.ideal t,.ideal (.ideal t),0⟩

variable {T : Type} [Fintype T] {length : Nat} {e : Space}

def eval (ρ : Nat → Density (.tensor (IdealKey.register T length) e)) : Term →
    Density (.tensor (IdealKey.register T length) e)
  | .state n => ρ n
  | .ideal t => IdealKey.idealize (eval ρ t)

def model (ρ : Nat → Density (.tensor (IdealKey.register T length) e)) : Model presentation where
  Carrier j := StateApprox (eval ρ j.left) (eval ρ j.right) j.error
  operation := fun r h => by
    cases r with
    | refl t => exact StateApprox.refl _
    | symm t u ε => exact StateApprox.symm (h 0)
    | trans t u v ε δ => exact StateApprox.trans (h 0) (h 1)
    | ideal t u ε => exact IdealKey.idealize_approx (h 0)
    | fixed t => exact IdealKey.ideal_secure (eval ρ t)

theorem sound (ρ : Nat → Density (.tensor (IdealKey.register T length) e))
    {Γ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (h : ∀ i, (model ρ).Carrier (Γ.claim i)) : (model ρ).Carrier j := d.eval (model ρ) h

theorem interpretation_substitute (ρ : Nat → Density (.tensor (IdealKey.register T length) e))
    {Γ Δ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model ρ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model ρ) h =
      d.eval (model ρ) (fun i => (r i).eval (model ρ) h) :=
  Derivation.eval_substitute (model ρ) h d r

/-- A real-to-ideal error premise composes with the exact fixed-point theorem. -/
def fixedComposition (t : Term) (ε : ℝ) :
    Derivation presentation (Logic.Context.singleton ⟨t,.ideal t,ε⟩)
      ⟨t,.ideal (.ideal t),ε+0⟩ :=
  .apply (T := presentation) (.trans t (.ideal t) (.ideal (.ideal t)) ε 0) (fun i =>
    if hi : i = 0 then by subst i; exact .hypothesis (T := presentation) 0
    else by
      change Fin 2 at i
      change i ≠ (0 : Fin 2) at hi
      have h1 : i = 1 := by omega
      subst i
      exact .apply (T := presentation) (.fixed t) (fun i => Fin.elim0 i))

end
end Foundation.Quantum.QKD.IdealKeyLogic
