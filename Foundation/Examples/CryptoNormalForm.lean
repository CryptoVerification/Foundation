import Foundation.Crypto.Meta.NormalForm
import Foundation.Examples.CryptoLogic

namespace CryptoLogic.Examples.NormalForms

open Machine Machine.Examples

/- Separate transport nodes expose the difference between derivation shape
and the single registered route recovered by the normal-form theorem. -/
def nestedTree : DerivationTree signature context .source bitFamily :=
  DerivationTree.transport (S := signature) (Γ := context)
    (ReductionExpr.primitive (L := language) Primitive.append) bitFamily
    (DerivationTree.transport (S := signature) (Γ := context)
      (ReductionExpr.primitive (L := language) Primitive.constant) bitFamily
      (DerivationTree.hypothesis (S := signature) (Γ := context) ⟨1, by decide⟩))

example : nestedTree.normalForm.index.val = 1 := rfl

example : nestedTree.normalForm.route =
    .seq (ReductionExpr.primitive (L := language) Primitive.append)
      (.seq (ReductionExpr.primitive (L := language) Primitive.constant)
        (ReductionExpr.identity (L := language) Object.target)) := rfl

/- Flattening keeps the exact one-step budget of the constant compiler, rather
than adding a generic bound for the original two transport nodes. -/
example (m : Nat) :
    (nestedTree.normalForm.route.eval signature).budget sourceProgram m = 1 := rfl

example : (nestedTree.normalForm.route.eval signature).reduction.loss =
    nestedTree.extract.certificate.reduction.loss := by
  exact congrArg (fun c => c.reduction.loss) nestedTree.route_eval

example : Nonempty (Derivation signature context .source bitFamily) := by
  apply derivable_iff_registered_route.mpr
  exact ⟨⟨1, by decide⟩, route, rfl⟩

/- Code reconstruction from an explicit normal form remains executable even
though the semantic signature is noncomputable. -/
def explicitNormalForm : NormalForm signature context .source bitFamily :=
  ⟨⟨1, by decide⟩, route, rfl⟩

/-- info: true -/
#guard_msgs in
#eval explicitNormalForm.toDerivation.compiler.run randomOutputBit == haltImmediately

example (p : Program) :
    substituted.compiler.run p =
      (replacement derivation.extract.index).compiler.run (derivation.compiler.run p) :=
  derivation.substitute_run replacement p

/- The existing concrete ElGamal derivation also has a registered route; this
proof does not expand its 147-billion-instruction output. -/
example (F) : Nonempty (NormalForm
    (ElGamal.Logic.signature ElGamal.PrimeOrderRepresentation.chooseNormalizer)
    (ElGamal.Logic.context ElGamal.PrimeOrderRepresentation.chooseNormalizer F)
    .indCPA F) :=
  ⟨(ElGamal.PrimeOrderRepresentation.logicDerivation F).normalForm⟩

end CryptoLogic.Examples.NormalForms
