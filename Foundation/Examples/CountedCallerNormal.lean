import Foundation.Crypto.Semantics.Oracle.CountedCaller
import Foundation.Examples.OneUseAdaptiveSecrecy

/-! Normal encryption from the actual counted caller's blank separator.
The retained marker prefix is arbitrary; normal preparation executes the
entry branch, delimiter move, jump, copy, and rewind before encryption. -/
namespace Foundation.CountedCallerNormalExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (past : List (Option Bool)) (hWidth : width ≠ 0)

include hWidth in
theorem nonempty (bits : Bits width) : bits.toList ≠ [] := by
  intro he
  have hl : width = 0 := by simpa using congrArg List.length he
  exact hWidth hl

def machine (bits : Bits width) := (CountedCaller.ready past bits.toList).rebasePc CountedCaller.before.length

noncomputable def before (message key : Bits width) :=
  (CountedCaller.preparation Machine.OneTimePad.Prepared.listProcedure.code oracle
    (Machine.PairPreparation.operand [] key.toList []) state trace).reindex (fun _ : Unit => (past, message.toList))

theorem before_budget (message key : Bits width) : (before oracle state trace past message key).budget () = 11 * width + 8 := by
  change 11 * message.toList.length + 8 = _
  simp

theorem before_costed (message key : Bits width) :
    (before oracle state trace past message key).costed () = PMF.pure ((), 11 * width + 8) := by
  simp [before, CountedCaller.preparation, Procedure.reindex, Procedure.ofFixed, PMF.pure_map]

include hWidth in
theorem handoff (message key : Bits width) (start result : Unit)
    (_ : result ∈ ((before oracle state trace past message key).semantics start).support) :
    (OneUseAdaptiveSecrecyExamples.normal CountedCaller.code oracle
      (fun _ : Unit => state) (fun _ => trace) (fun _ => message) (fun _ => machine past)
      (fun _ bits => CountedCaller.ready_active past bits.toList)
      (fun _ bits => CountedCaller.ready_call past bits.toList)
      (fun _ bits => CountedCaller.ready_tape past bits.toList (nonempty hWidth bits))
      (fun _ bits => CountedCaller.ready_halt past bits.toList) key).entry result =
      (before oracle state trace past message key).exit start result := rfl

noncomputable def ciphertext (message : Bits width) :=
  (uniform (Bits width)).bind (fun key =>
    (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code CountedCaller.code oracle)
      (44 * width + 42) (.source false (Machine.PairPreparation.operand [] key.toList [])
        ⟨state, .running (CountedCaller.waiting past [] message.toList), trace⟩)).map OneUseAdaptiveSecrecyExamples.packet)

include hWidth in
theorem perfect_secrecy (left right : Bits width) (observer : List Bool → PMF Bool) :
    (ciphertext oracle state trace past left).bind observer =
      (ciphertext oracle state trace past right).bind observer := by
  apply OneUseAdaptiveSecrecyExamples.machine_perfect_secrecy CountedCaller.code oracle
    (fun _ : Unit => state) (fun _ => trace) (fun _ => machine past)
    (fun _ bits => CountedCaller.ready_active past bits.toList)
    (fun _ bits => CountedCaller.ready_call past bits.toList)
    (fun _ bits => CountedCaller.ready_tape past bits.toList (nonempty hWidth bits))
    (fun _ bits => CountedCaller.ready_halt past bits.toList)
    (fun _ => left) (fun _ => right)
    (before oracle state trace past left) (before oracle state trace past right)
    (handoff oracle state trace past hWidth left) (handoff oracle state trace past hWidth right)
    () (PMF.pure ((), 11 * width + 8))
    (before_costed oracle state trace past left) (before_costed oracle state trace past right)
    (44 * width + 42)
  · intro key
    rw [before_budget]
    omega
  · intro key
    rw [before_budget]
    omega

end Foundation.CountedCallerNormalExamples
