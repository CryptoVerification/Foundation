import Foundation.Crypto.Semantics.Oracle.OneUseCodeRelocation
import Foundation.Examples.InputRejectionThenEncrypt

/-! Reuse a proved rejection/input-copy/normal-encryption block at any
caller-code offset. Leading code is present but its execution is separate. -/
namespace Foundation.RelocatedInputRejectionExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat} (before : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (message : Bits width)
    (key : Bits width) (hWidth : width ≠ 0)

noncomputable def preparation :=
  CodeRelocation.oneUseProcedure before BalancedCopy.code Machine.OneTimePad.Prepared.listProcedure.code oracle
    (InputRejectionThenEncryptExamples.before oracle state trace message key hWidth)

theorem preparation_budget : (preparation before oracle state trace message key hWidth).budget () = 11 * width + 34 :=
  InputRejectionThenEncryptExamples.before_budget oracle state trace message key hWidth

theorem preparation_costed : (preparation before oracle state trace message key hWidth).costed () =
    (InputRejectionThenEncryptExamples.before oracle state trace message key hWidth).costed () := rfl

theorem packet_relocation (base : Nat) (source : OneUseSource.Control State) :
    OneUseAdaptiveSecrecyExamples.packet (CodeRelocation.oneUse base source) =
      OneUseAdaptiveSecrecyExamples.packet source := by
  cases source with
  | source used key source =>
      rcases source with ⟨state, sourceControl, trace⟩
      cases sourceControl <;> rfl
  | handling used saved state trace request handler => rfl

noncomputable def ciphertext :=
  (uniform (Bits width)).bind (fun key =>
    (TimedExecution.eval
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code (CodeRelocation.host before BalancedCopy.code) oracle)
      (44 * width + 68)
      (CodeRelocation.oneUse before.length (.source false (Machine.PairPreparation.operand [] key.toList [])
        ⟨state, .running (InputRejectionThenEncryptExamples.initial message), trace⟩))).map
        OneUseAdaptiveSecrecyExamples.packet)

theorem ciphertext_eq : ciphertext before oracle state trace message =
    (uniform (Bits width)).bind (fun key =>
      (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code BalancedCopy.code oracle)
        (44 * width + 68) (.source false (Machine.PairPreparation.operand [] key.toList [])
          ⟨state, .running (InputRejectionThenEncryptExamples.initial message), trace⟩)).map
        OneUseAdaptiveSecrecyExamples.packet) := by
  unfold ciphertext
  congr 1
  funext key
  rw [CodeRelocation.one_use_eval, PMF.map_comp]
  simp only [Function.comp_def, packet_relocation]

include hWidth in
theorem perfect_secrecy (left right : Bits width) (observer : List Bool → PMF Bool) :
    (ciphertext before oracle state trace left).bind observer =
      (ciphertext before oracle state trace right).bind observer := by
  rw [ciphertext_eq, ciphertext_eq]
  exact InputRejectionThenEncryptExamples.machine_perfect_secrecy oracle state trace hWidth left right observer

end Foundation.RelocatedInputRejectionExamples
