import Foundation.Constructions.Symmetric.PRGOptimized
import Foundation.Crypto.Meta.General.CertifiedPipeline

/-! Arbitrarily deep administrative compiler chains around the optimized PRG
reduction have an explicit fixed-code extraction. Depth may depend on the
security parameter: no constant-depth or polynomial-depth premise is used.
This result is for the specified appended-halt passes, not arbitrary passes
or arbitrary parameter-dependent cryptographic proof families. -/
namespace Foundation.Symmetric.Generator.Optimized.Pipeline
open Foundation.Probability CryptoLogic.General
set_option backward.isDefEq.respectTransparency false

def pass (code : Mode × Machine.Masking.Code) : Mode × Machine.Masking.Code :=
  (code.1, Machine.Masking.appendHalt code.2)

theorem eval_pass (code : Mode × Machine.Masking.Code)
    (header left right challenge : List Bool) (fuel : Nat) :
    eval (pass code) (Machine.Masking.initial (pass code).2 header left right challenge) fuel =
      eval code (Machine.Masking.initial code.2 header left right challenge) fuel := by
  simp only [pass, Machine.Masking.initial_appendHalt]
  cases code with
  | mk mode code =>
      cases mode with
      | original => exact Machine.Masking.eval_appendHalt code _ fuel
      | fused => exact Machine.Masking.Fused.eval_appendHalt code _ fuel

/-- Finite, executable compiler syntax. No instance, family, or budget is
passed to an emitted compiler; the depth is a compiler construction input. -/
def compiler : Nat → Compiler system true true
  | 0 => Compiler.identity (K := system) true
  | depth + 1 => .comp (compiler depth) (.primitive .appendHalt)

theorem eval_compiler (code : Mode × Machine.Masking.Code) (depth : Nat)
    (header left right challenge : List Bool) (fuel : Nat) :
    eval ((compiler depth).run code)
      (Machine.Masking.initial ((compiler depth).run code).2 header left right challenge) fuel =
      eval code (Machine.Masking.initial code.2 header left right challenge) fuel := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change eval (pass ((compiler depth).run code))
        (Machine.Masking.initial (pass ((compiler depth).run code)).2 header left right challenge) fuel = _
      exact (eval_pass _ _ _ _ _ _).trans ih

noncomputable section

def administrative (G : Generator) : CertifiedTransform (target G) (target G) where
  transform := ⟨fun I => I, fun _ A => A⟩
  compiler := .primitive .appendHalt
  mapWitness := fun F A W => {
    code := pass W.code
    resources := W.resources
    executes := by
      refine ⟨W.executes.1, ?_⟩
      intro n challenge finish hf
      change finish ∈ (eval (pass W.code)
        (Machine.Masking.initial (pass W.code).2 _ _ _ _) _).support at hf
      rw [eval_pass] at hf
      exact W.executes.2 n challenge finish hf
    realizes := by
      intro n challenge
      rw [eval_pass]
      exact W.realizes n challenge
    admissible := W.admissible }
  code_eq := by intros; rfl

def stage (G : Generator) (_i : Nat) := administrative G

theorem compiler_eq (G : Generator) (depth : Nat) :
    CertifiedPipeline.compiler (stage G) depth = compiler depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change Compiler.comp (CertifiedPipeline.compiler (stage G) depth) _ = _
      rw [ih]
      rfl

theorem resources (G : Generator) (input : CertifiedPipeline.Entry (target G)) (depth : Nat) :
    (CertifiedPipeline.run (stage G) input depth).witness.resources = input.witness.resources := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact ih

/-- The fixed witness is constructed directly from the fixed source attack
code. It realizes the whole family of deep emitted programs, even when their
depth is not polynomial. Proof-normalization/extraction runtime and the
storage of unnormalized code are not claimed bounded by this theorem. -/
theorem uniform_extraction (G : Generator) (time : Nat → Nat)
    (ht : PolynomiallyBounded time) (hL : PolynomiallyBounded G.outputLength)
    (side : Bool) (F A) (W : (source G time).Witness F A) (depth : Nat → Nat) :
    ∃ fixed : (target G).Witness ((semantic G side).mapFamily F)
        ((semantic G side).mapAdversaryFamily F A),
      fixed.code = (Mode.fused, Machine.Masking.compile side W.code) ∧
      fixed.resources = Optimized.time G time ∧
      ∀ n (challenge : Bits (G.outputLength n)),
        eval ((compiler (depth n)).run fixed.code)
          (Machine.Masking.initial ((compiler (depth n)).run fixed.code).2 (G.header n (F n))
            (F n).1.toList (F n).2.toList challenge.toList) (fixed.resources n) =
        eval fixed.code (Machine.Masking.initial fixed.code.2 (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) (fixed.resources n) := by
  refine ⟨(implementation G time ht hL .fused side).mapWitness F A W, rfl, rfl, ?_⟩
  intro n challenge
  exact eval_compiler _ _ _ _ _ _ _

end
end Foundation.Symmetric.Generator.Optimized.Pipeline
