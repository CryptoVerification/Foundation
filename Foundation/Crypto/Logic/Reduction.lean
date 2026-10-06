import Foundation.Crypto.Semantics.Machine.CertifiedReduction

namespace CryptoLogic

universe u v w a b

set_option linter.checkUnivs false in
/-- Executable object and primitive names, with their finite compiler syntax.
No semantic goal, adversary function, or analysis certificate is stored here. -/
structure Language where
  Object : Type a
  Primitive : Object → Object → Type b
  primitiveCompiler : ∀ {X Y}, Primitive X Y → Machine.ProgramCompiler

set_option linter.checkUnivs false in
/-- Object and primitive names with a certified interpretation. Executable
compiler syntax is supplied separately from semantic certificates, so code
construction does not evaluate adversaries, families, or runtime analysis.
Each expression uses finitely many names; the signature need not be finite. -/
structure Signature (L : Language.{a, b}) where
  interpret : L.Object → SecurityObject.{u, v, w}
  certificate : ∀ {X Y}, L.Primitive X Y → CertifiedReduction (interpret X) (interpret Y)
  compiler_eq : ∀ {X Y} (e : L.Primitive X Y),
    (certificate e).compiler = L.primitiveCompiler e

/-- The three reduction rules: identity, a registered primitive, and sequential
composition. No arbitrary semantic reduction can be inserted into an expression. -/
inductive ReductionExpr (L : Language.{a, b}) :
    L.Object → L.Object → Type (max a b) where
  | identity (X) : ReductionExpr L X X
  | primitive {X Y} (e : L.Primitive X Y) : ReductionExpr L X Y
  | seq {X Y Z} (first : ReductionExpr L X Y) (second : ReductionExpr L Y Z) :
      ReductionExpr L X Z

namespace ReductionExpr

variable {L : Language.{a, b}}

/-- Structural, executable construction of a finite code compiler. -/
def compiler {X Y} : ReductionExpr L X Y → Machine.ProgramCompiler
  | .identity _ => .identity
  | .primitive e => L.primitiveCompiler e
  | .seq first second => .comp first.compiler second.compiler

/-- Interpret syntax as a certified quantitative reduction. -/
def eval {X Y} (r : ReductionExpr L X Y) (S : Signature.{u, v, w} L) :
    CertifiedReduction (S.interpret X) (S.interpret Y) :=
  match r with
  | .identity X => CertifiedReduction.id (S.interpret X)
  | .primitive e => S.certificate e
  | .seq first second => (first.eval S).comp (second.eval S)

theorem eval_compiler {X Y} (r : ReductionExpr L X Y) (S : Signature.{u, v, w} L) :
    (r.eval S).compiler = r.compiler := by
  induction r with
  | identity X => rfl
  | primitive e => exact S.compiler_eq e
  | seq first second ihFirst ihSecond =>
      change Machine.ProgramCompiler.comp (first.eval S).compiler (second.eval S).compiler =
        Machine.ProgramCompiler.comp first.compiler second.compiler
      rw [ihFirst, ihSecond]

/-- Reassociation preserves emitted code, not necessarily syntactic compiler
trees or the numerical majorants used by a particular primitive certificate. -/
theorem seq_assoc_run {X Y Z W} (r : ReductionExpr L X Y)
    (s : ReductionExpr L Y Z) (t : ReductionExpr L Z W) (p : Machine.Program) :
    ((r.seq s).seq t).compiler.run p = (r.seq (s.seq t)).compiler.run p := rfl

end ReductionExpr
end CryptoLogic
