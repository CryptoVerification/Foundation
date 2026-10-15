import Foundation.Crypto.Logic.Polygraph.Interpretation

/-! Every emitted code is the code carried by its full execution certificate.
Resource types, values, stopping proofs, and distribution realizations are
inherited from the explicitly selected reconstructed proof tree. -/
namespace CryptoLogic.Polygraph.Derivation

open General
universe u v a b p
set_option linter.checkUnivs false

variable {K : CodeSystem} {L : General.Language.{a, b} K}
  {P : Presented.Parameters.{a, b, p} L} {Γ : Presented.Context P}
  {S : General.Signature.{u, v} L}

def runWitnesses (M : Presented.Interpretation P S) {X F} (d : Derivation P Γ X F)
    (A) (W : (S.interpret X).Witness (M.family F) A) :=
  M.runWitnesses (toPresented d) A W

theorem runWitnesses_emitted (M : Presented.Interpretation P S) {X F}
    (d : Derivation P Γ X F) (A) (W : (S.interpret X).Witness (M.family F) A) :
    (runWitnesses M d A W).map CertifiedOutput.emitted = run d W.code :=
  M.runWitnesses_emitted (toPresented d) A W

@[simp] theorem runWitnesses_ofPresented (M : Presented.Interpretation P S) {X F}
    (d : Presented.Derivation P Γ X F) (A) (W : (S.interpret X).Witness (M.family F) A) :
    runWitnesses M (ofPresented d) A W = M.runWitnesses d A W := by
  simp [runWitnesses]

end CryptoLogic.Polygraph.Derivation
