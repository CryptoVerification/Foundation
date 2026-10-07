import Foundation.Crypto.Logic.Presented.CompositeRule
import Foundation.Examples.PureLogic
import Foundation.Examples.CryptoLogic
import Foundation.Crypto.Logic.General.Legacy

/-! Derived-rule expansion checked with observable compiler order and actual
native execution witnesses. The first compiler appends a halt; the second
replaces the whole code by a constant-answer program. -/
namespace Foundation.Logic.TranslationExamples

open Foundation.Logic.Examples
set_option backward.isDefEq.respectTransparency false

example : (Translation.identity theory).translate proof = proof := Translation.translate_identity proof
example : ((Translation.identity theory).comp (Translation.identity theory)).translate proof = proof := rfl
example : (Translation.identity theory).translate (proof.substitute (fun _ => closed)) =
    ((Translation.identity theory).translate proof).substitute
      (fun _ => (Translation.identity theory).translate closed) :=
  Translation.translate_substitute _ _ _
example : ((Translation.identity theory).translate proof).eval numeric (fun _ => 2) =
    proof.eval ((Translation.identity theory).pullback numeric) (fun _ => 2) :=
  Translation.eval_translate _ _ _ _

end Foundation.Logic.TranslationExamples

namespace CryptoLogic.Presented.CompositeExamples

open General General.Backends Machine Machine.Examples
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev language := General.Legacy.language (General.Legacy.Unary.language Examples.language)
noncomputable abbrev signature := General.Legacy.signature (General.Legacy.Unary.signature Examples.signature)

-- These are two primitive reductions, not an identity used to fill a slot.
def first : General.ReductionExpr language Examples.Object.source Examples.Object.middle :=
  General.Legacy.expression (L := General.Legacy.Unary.language Examples.language) (.primitive .append)
def second : General.ReductionExpr language Examples.Object.middle Examples.Object.target :=
  General.Legacy.expression (L := General.Legacy.Unary.language Examples.language) (.primitive .constant)

-- A fixed computable parameter and proof; semantic families come later.
abbrev parameters : Presented.Parameters language where
  Family := fun _ => Unit
  unary := fun _ _ => ()
  left := fun e => nomatch e.down
  right := fun e => nomatch e.down

abbrev context : Foundation.Logic.Context (CompositeRule.presentation parameters) where
  length := 2
  claim := Fin.cases ⟨Examples.Object.middle, ()⟩ (fun _ => ⟨Examples.Object.target, ()⟩)

def proof : Foundation.Logic.Derivation (CompositeRule.presentation parameters) context
    ⟨Examples.Object.source, ()⟩ :=
  Foundation.Logic.Derivation.apply (T := CompositeRule.presentation parameters)
    (CompositeRule.Rule.seq first second ())
    (fun _ => Foundation.Logic.Derivation.hypothesis (T := CompositeRule.presentation parameters)
      (Γ := context) 1)

def expanded := (CompositeRule.expansion (P := parameters)).translate proof

private theorem unaryFamily (r : CryptoLogic.ReductionExpr CryptoLogic.Examples.language X Y) :
    (r.eval CryptoLogic.Examples.signature).reduction.mapFamily Machine.Examples.bitFamily =
      Machine.Examples.bitFamily := by
  induction r with
  | identity X => rfl
  | primitive e => cases e <;> rfl
  | seq r s hr hs =>
      change (s.eval CryptoLogic.Examples.signature).reduction.mapFamily
        ((r.eval CryptoLogic.Examples.signature).reduction.mapFamily Machine.Examples.bitFamily) = _
      rw [hr, hs]

noncomputable def interpretation : Presented.Interpretation parameters signature where
  family := fun _ => Examples.bitFamily
  unary := by
    intro X Y r _
    induction r with
    | identity X => rfl
    | primitive e => exact (unaryFamily e).symm
    | seq r s hr hs =>
        change _ = (s.eval signature).reduction.mapFamily ((r.eval signature).reduction.mapFamily _)
        rw [← hr (), ← hs ()]
  left := by intro X Y Z e _; nomatch e.down
  right := by intro X Y Z e _; nomatch e.down

/-- info: true -/
#guard_msgs in
#eval (Presented.Derivation.run expanded randomOutputBit).map
  (fun (i, code) => match code with
    | ⟨.native, p⟩ => (i, Program.encode p == Program.encode haltImmediately)
    | _ => (i, false)) == [(1, true)]

-- Reversing the order would append an extra instruction.
example : first.compiler.run (second.compiler.run randomOutputBit) ≠
    second.compiler.run (first.compiler.run randomOutputBit) := by
  change (haltImmediately ++ [.halt] : Machine.Program) ≠ haltImmediately
  decide

example (p : Machine.Program) :
    proof.eval (CompositeRule.compactCode parameters context.length)
      (fun i code => [(i, ⟨language.machine (context.claim i).object, code⟩)]) p =
      (Presented.Derivation.plan expanded).run p :=
  congrFun (CompositeRule.code_preserved proof) p

example (ε : Fin 2 → Nat → ℝ≥0∞) (n : Nat) :
    (interpretation.loss expanded).eval ε n = ε 1 n := rfl

-- The whole certified output retains an actual stopping budget, not only
-- the emitted code. The replacement compiler needs exactly one transition.
noncomputable def witness := General.Backends.Native.witness Examples.sourceWitness

example : (interpretation.runWitnesses expanded _ witness).map
    (fun out => out.witness.resources 0) = [1] := rfl

example : (interpretation.runWitnesses expanded _ witness).map CertifiedOutput.emitted =
    [(1, ⟨Kind.native, haltImmediately⟩)] := by
  rw [Interpretation.runWitnesses_emitted]
  rfl

end CryptoLogic.Presented.CompositeExamples
