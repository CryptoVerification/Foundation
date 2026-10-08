import Foundation.Crypto.Semantics.Machine.FlaggedBlockXorComponent

/-! Compile native masking followed by arbitrary finite internal processing.
Both tapes, including retained secret input, are passed on exactly. Therefore
this interface is not a public adversary interface or a security theorem. -/
namespace Machine.FlaggedBlockXor.Component
open Foundation.Probability TimedExecution
universe u
variable {Output : Type u}

noncomputable def continueWith (Q : NativeComponent Configuration Output)
    (entry : ∀ machine, Q.procedure.execution.entry machine = machine.resumeAt 0)
    (cap : Input → Nat)
    (bounded : ∀ input, Q.procedure.execution.budget (final input.key input.message) ≤ cap input) :
    TypedNativeComposition.Link component.procedure Q.procedure :=
  component.link Q (fun _ machine => {machine.resumeAt 36 with halted := true})
    (by
      intro input output h
      change output ∈ (component.procedure.execution.semantics input).support at h
      rw [semantics, PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun _ machine => machine)
    (by
      intro input output _
      rw [entry]
      simp only [Configuration.resumeAt, Configuration.rebasePc, Configuration.mk.injEq,
        Nat.add_zero, and_true, true_and]
      exact ⟨rfl, rfl⟩)
    cap (by
      intro input output h
      rw [semantics, PMF.mem_support_pure_iff] at h
      subst output
      exact bounded input)

theorem continue_code (Q : NativeComponent Configuration Output) (entry) (cap) (bounded) :
    (continueWith Q entry cap bounded).code = FlaggedBlockXor.code.followedBy Q.procedure.code := rfl

theorem continue_budget (Q : NativeComponent Configuration Output) (entry) (cap) (bounded) (input : Input) :
    (continueWith Q entry cap bounded).native.execution.budget input =
      24 * input.message.length + cap input + 9 := by
  rw [TypedNativeComposition.Link.budget]
  change 24 * input.message.length + 8 + cap input + 1 = _
  omega

theorem continue_semantics (Q : NativeComponent Configuration Output) (entry) (cap) (bounded) (input : Input) :
    (continueWith Q entry cap bounded).native.execution.semantics input =
      (Q.procedure.execution.semantics (final input.key input.message)).map (fun result =>
        {(Q.procedure.execution.exit (final input.key input.message) result).resumeAt
          (37 + Q.procedure.code.length + 2) with halted := true}) := by
  rw [TypedNativeComposition.Link.semantics, semantics, PMF.pure_bind]
  rfl

theorem continue_operational (Q : NativeComponent Configuration Output) (entry) (cap) (bounded) :
    TimedExecution.Procedure.Operational (continueWith Q entry cap bounded).native.execution :=
  (continueWith Q entry cap bounded).operational

end Machine.FlaggedBlockXor.Component
