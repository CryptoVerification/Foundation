import Foundation.Crypto.Semantics.Oracle.OneUsePreparation
import Foundation.Crypto.Semantics.Oracle.OneUseRejection

/-! Actual call capture composes with any compatible handler contract.
Request extraction is charged and uses the source's existing physical tape. -/
namespace CryptoOracle.Interactive.OneUseSource
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request)

noncomputable def capture : Procedure (step native code oracle) Unit Unit :=
  Procedure.ofFixed _
    (fun _ => .source spent key ⟨state, .running machine, trace⟩)
    (fun _ _ => .handling spent machine.advance state trace request
      (if spent then .tagging key machine.outputTape (.start none)
       else .preparing (.preparing (.reading key machine.outputTape {}))))
    (fun _ => PMF.pure ()) (fun _ => 2 * request.length + 4)
    (fun _ => by simpa only [PMF.pure_map] using
      (call_entry native code oracle spent key machine state trace request before after hActive hCall hTape))

variable {Output : Type v} (handler : Procedure (step native code oracle) Unit Output)
    (hEntry : handler.entry () = .handling spent machine.advance state trace request
      (if spent then .tagging key machine.outputTape (.start none)
       else .preparing (.preparing (.reading key machine.outputTape {}))))

/-- Caller code, opaque state and trace are unrestricted. -/
noncomputable def invocation :=
  (capture native code oracle spent key machine state trace request before after hActive hCall hTape).seq
    (handler.reindex (fun _ => ())) (fun _ _ _ => hEntry)
    (fun _ => handler.budget ()) (fun _ _ _ => Nat.le_refl _)

theorem invocation_budget :
    (invocation native code oracle spent key machine state trace request before after hActive hCall hTape handler hEntry).budget () =
      2 * request.length + 4 + handler.budget () := rfl

theorem invocation_semantics :
    (invocation native code oracle spent key machine state trace request before after hActive hCall hTape handler hEntry).semantics () =
      (handler.semantics ()).map (fun output => ((), output)) := by
  simp [invocation, capture, Procedure.seq, Procedure.reindex, Procedure.ofFixed, PMF.pure_bind, Function.comp_def]

theorem invocation_distribution :
    ((invocation native code oracle spent key machine state trace request before after hActive hCall hTape handler hEntry).costed ()).map
      (fun result => (invocation native code oracle spent key machine state trace request before after hActive hCall hTape handler hEntry).exit () result.1) =
      (handler.costed ()).map (fun result => handler.exit () result.1) := by
  have h := congrArg (fun distribution => distribution.map
    ((invocation native code oracle spent key machine state trace request before after hActive hCall hTape handler hEntry).exit ()))
    ((invocation native code oracle spent key machine state trace request before after hActive hCall hTape handler hEntry).correct ())
  have k := congrArg (fun distribution => distribution.map (handler.exit ())) (handler.correct ())
  rw [invocation_semantics] at h
  simp only [PMF.map_comp, Function.comp_def] at h k
  have he : ∀ output,
      (invocation native code oracle spent key machine state trace request before after hActive hCall hTape handler hEntry).exit () ((), output) =
      handler.exit () output := by intro output; rfl
  simp only [he] at h
  exact h.trans k.symm

section Spent
noncomputable def spentRejection : Procedure (step native code oracle) Unit Unit :=
  Procedure.ofFixed _
    (fun _ => .handling true machine.advance state trace request (.tagging key machine.outputTape (.start none)))
    (fun _ _ => .source true key (NativeCallback.resumed machine.advance state trace request [false]))
    (fun _ => PMF.pure ()) (fun _ => 18)
    (fun _ => by simpa only [PMF.pure_map] using
      (spent_reply native code oracle machine.advance state trace request key machine.outputTape))

noncomputable def spentInvocation :=
  invocation native code oracle true key machine state trace request before after hActive hCall hTape
    (spentRejection native code oracle key machine state trace request) (by rfl)

theorem spentInvocation_budget :
    (spentInvocation native code oracle key machine state trace request before after hActive hCall hTape).budget () =
      2 * request.length + 22 := by
  change (2 * request.length + 4) + 18 = _
  omega
theorem spentInvocation_distribution :
    ((spentInvocation native code oracle key machine state trace request before after hActive hCall hTape).costed ()).map
      (fun result => (spentInvocation native code oracle key machine state trace request before after hActive hCall hTape).exit () result.1) =
      PMF.pure (.source true key (NativeCallback.resumed machine.advance state trace request [false])) := by
  unfold spentInvocation
  rw [invocation_distribution]
  simp [spentRejection, Procedure.ofFixed, PMF.pure_map]
end Spent

section Rejected
variable (input : Machine.PreparationCheck.FailureInput)
    (hSourceTape : machine.outputTape = RequestExport.packetTape [] input.secondTail input.second)

noncomputable def rejectedInvocation :=
  invocation native code oracle false
    (Machine.PairPreparation.operand [] input.first input.firstTail)
    machine state trace input.second [] input.secondTail hActive hCall hSourceTape
    (OneUseRejection.whole native code oracle machine.advance state trace input.second input)
    (by
      simp only [hSourceTape, OneUseRejection.whole, OneUseRejection.preparation,
        OneUseRejection.embedFailure, Procedure.seq, Procedure.liftBoundary, Procedure.ofFixed]
      rfl)

theorem rejectedInvocation_budget :
    (rejectedInvocation native code oracle machine state trace hActive hCall input hSourceTape).budget () =
      2 * input.second.length + 12 * Machine.PreparationCheck.consumed input + 29 := by
  unfold rejectedInvocation
  rw [invocation_budget, OneUseRejection.budget]
  omega
theorem rejectedInvocation_distribution :
    ((rejectedInvocation native code oracle machine state trace hActive hCall input hSourceTape).costed ()).map
      (fun result => (rejectedInvocation native code oracle machine state trace hActive hCall input hSourceTape).exit () result.1) =
      PMF.pure (.source false (Machine.PairPreparation.operand [] input.first input.firstTail)
        (NativeCallback.resumed machine.advance state trace input.second [false])) := by
  unfold rejectedInvocation
  rw [invocation_distribution, OneUseRejection.distribution]
  rfl
end Rejected
end CryptoOracle.Interactive.OneUseSource
