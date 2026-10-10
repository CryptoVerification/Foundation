import Foundation.Quantum.QKD.QuantumErrorSampling
import Foundation.Logic.Presentation

/-! Finite classical-to-quantum sampling inference. Its sole input bound is
classical and pointwise; the actual good-support approximant is constructed by
the model. These are independent rule-design choices, not a transcription of
a calculus in Heunen or an arbitrary semantic truth rule. -/
namespace Foundation.Quantum.QKD.QuantumSamplingLogic
noncomputable section
open Foundation.Logic PureProjection
set_option backward.isDefEq.respectTransparency false

inductive Claim where
  | classical (ε : ℝ)
  | sampled (ε : ℝ)
  | processed (c : Nat) (ε : ℝ)

inductive Rule where
  | lift (ε : ℝ)
  | post (c : Nat) (ε : ℝ)
  | weaken (ε δ : ℝ) (h : ε ≤ δ)

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule
  arity _ := 1
  premise := fun
    | .lift ε => fun _ => .classical ε
    | .post _ ε => fun _ => .sampled ε
    | .weaken ε _ _ => fun _ => .sampled ε
  conclusion := fun
    | .lift ε => .sampled (Real.sqrt ε)
    | .post c ε => .processed c ε
    | .weaken _ δ _ => .sampled δ

variable {a b : Space} {S : Type} [Fintype S]

def model (p : PMF S) (good : S → a.Basis → Prop) [∀ s, DecidablePred (good s)]
    (v : a.Basis → ℂ) (hv : bracket v v = 1) (fallback : S → a.Basis)
    (C : Nat → Channel (Guessing.publicSpace S a) b) : Model presentation where
  Carrier := fun
    | .classical ε => ∀ i, (Foundation.Probability.eventProb p (fun s => ¬ good s i)).toReal ≤ ε
    | .sampled ε => OperatorApprox (QuantumSampling.real p v) (QuantumSampling.ideal p good v fallback) ε
    | .processed c ε => OperatorApprox (C c |>.toKraus.apply (QuantumSampling.real p v))
        (C c |>.toKraus.apply (QuantumSampling.ideal p good v fallback)) ε
  operation := fun r hs => by
    cases r with
    | lift ε => exact QuantumSampling.approximation p good v hv fallback ε (hs 0)
    | post c ε => exact (hs 0).postprocess (C c)
    | weaken ε δ h => exact (hs 0).weaken h

theorem sound (p : PMF S) (good : S → a.Basis → Prop) [∀ s, DecidablePred (good s)]
    (v : a.Basis → ℂ) (hv : bracket v v = 1) (fallback : S → a.Basis)
    (C : Nat → Channel (Guessing.publicSpace S a) b)
    {Γ : Context presentation} {j} (d : Derivation presentation Γ j)
    (hs : ∀ i, (model p good v hv fallback C).Carrier (Γ.claim i)) :
    (model p good v hv fallback C).Carrier j := d.eval _ hs

theorem interpretation_substitute (p : PMF S) (good : S → a.Basis → Prop) [∀ s, DecidablePred (good s)]
    (v : a.Basis → ℂ) (hv : bracket v v = 1) (fallback : S → a.Basis)
    (C : Nat → Channel (Guessing.publicSpace S a) b)
    {Γ Δ : Context presentation} {j} (d : Derivation presentation Γ j)
    (f : ∀ i, Derivation presentation Δ (Γ.claim i))
    (hs : ∀ i, (model p good v hv fallback C).Carrier (Δ.claim i)) :
    (d.substitute f).eval (model p good v hv fallback C) hs =
      d.eval (model p good v hv fallback C) (fun i => (f i).eval (model p good v hv fallback C) hs) :=
  Derivation.eval_substitute _ hs d f

def assumptions (ε : ℝ) : Context presentation := ⟨1,fun _ => .classical ε⟩

def proof (c : Nat) (ε : ℝ) : Derivation presentation (assumptions ε) (.processed c (Real.sqrt ε)) :=
  .apply (T := presentation) (.post c _) (fun _ =>
    .apply (T := presentation) (.lift ε) (fun _ => .hypothesis ⟨0,by change 0 < 1; decide⟩))

end
end Foundation.Quantum.QKD.QuantumSamplingLogic
