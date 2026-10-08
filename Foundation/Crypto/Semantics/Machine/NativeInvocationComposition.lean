import Foundation.Crypto.Semantics.Machine.NativeInvocationTime
import Foundation.Crypto.Semantics.BoundaryComposition

/-! Compose a native call with any terminating caller continuation, retaining
branch-dependent first-return times. No fixed-time or tight-budget premise
is used. The continuation executes from the actual returned configuration. -/
namespace Machine.NativeComponent
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Input : Type u} {Output : Type v} (P : NativeComponent Input Output)
    (pre suffix : Program) (returnPc : Nat)
    (layout : ∀ pc, pc < P.procedure.code.length → pre.length + pc ≠ returnPc)

theorem invocation_firstHalt_compose (input : Input) (lastFuel : Nat)
    (lastComplete : ∀ middle ∈ ((P.invocation pre suffix returnPc layout).costed input).support,
      ∀ result ∈ (runToBoundary (stepPMF (Program.withSubroutine pre P.procedure.code suffix returnPc))
        Configuration.halted lastFuel middle.1).support, result.1.halted = true) :
    runToBoundary (stepPMF (Program.withSubroutine pre P.procedure.code suffix returnPc))
      Configuration.halted (P.procedure.execution.budget input + lastFuel)
      ((P.procedure.execution.entry input).rebasePc pre.length) =
    ((P.invocation pre suffix returnPc layout).costed input).bind (fun middle =>
      (runToBoundary (stepPMF (Program.withSubroutine pre P.procedure.code suffix returnPc))
        Configuration.halted lastFuel middle.1).map (fun result => (result.1, middle.2 + result.2))) := by
  let valid := fun machine => ∃ source : Configuration,
    (source.halted = true ∨ source.pc < P.procedure.code.length) ∧
      machine = Program.subroutineState pre.length returnPc source
  have hCosted : (P.invocation pre suffix returnPc layout).costed input =
      runToBoundary (stepPMF (Program.withSubroutine pre P.procedure.code suffix returnPc))
        (fun machine => machine.pc == returnPc) (P.procedure.execution.budget input)
        ((P.procedure.execution.entry input).rebasePc pre.length) := by
    unfold invocation
    apply SubroutineContract.call_costed
  rw [hCosted] at lastComplete ⊢
  apply runToBoundary_compose _ _ _ valid _ _ _ _ _ _ _ lastComplete
  · intro machine hValid hBefore next hNext
    obtain ⟨source, hSource, rfl⟩ := hValid
    have hActive : source.halted = false := by
      cases hHalt : source.halted with
      | false => rfl
      | true => simp [Program.subroutineState, hHalt, Configuration.resumeAt] at hBefore
    have hInside : source.pc < P.procedure.code.length := hSource.resolve_left (by simp [hActive])
    simp only [Program.subroutineState, hActive, Bool.false_eq_true, ↓reduceIte] at hNext
    rw [Program.stepPMF_subroutineState pre P.procedure.code suffix returnPc layout
      P.closed source hInside hActive, PMF.mem_support_map_iff] at hNext
    obtain ⟨target, hTarget, rfl⟩ := hNext
    refine ⟨target, ?_, rfl⟩
    cases hHalt : target.halted with
    | true => exact Or.inl rfl
    | false =>
        right
        apply P.closed source target hInside _ hHalt
        rcases (mem_support_stepPMF_iff P.procedure.code source target).mp hTarget with h | ⟨h, _⟩
        · exact h
        · simp [hActive] at h
  · intro machine hValid _
    obtain ⟨source, _, rfl⟩ := hValid
    cases hHalt : source.halted <;>
      simp [Program.subroutineState, hHalt, Configuration.resumeAt, Configuration.rebasePc]
  · refine ⟨P.procedure.execution.entry input, Or.inr (P.entry input), ?_⟩
    simp [Program.subroutineState, P.active input]
  · intro middle hMiddle
    rw [← hCosted] at hMiddle
    have hLogical := (P.invocation pre suffix returnPc layout).result_support input middle hMiddle
    have hReturn := SubroutineContract.call_returns P.procedure pre suffix returnPc layout
      P.closed P.entry P.active P.halted input middle.1 hLogical
    simp [hReturn.1]

theorem invocation_then_halt (input : Input)
    (lookup : (Program.withSubroutine pre P.procedure.code suffix returnPc)[returnPc]? = some .halt) :
    runToBoundary (stepPMF (Program.withSubroutine pre P.procedure.code suffix returnPc))
      Configuration.halted (P.procedure.execution.budget input + 1)
      ((P.procedure.execution.entry input).rebasePc pre.length) =
      ((P.invocation pre suffix returnPc layout).costed input).map
        (fun result => ({result.1 with halted := true}, result.2 + 1)) := by
  have hOne (middle : Configuration × Nat)
      (hMiddle : middle ∈ ((P.invocation pre suffix returnPc layout).costed input).support) :
      runToBoundary (stepPMF (Program.withSubroutine pre P.procedure.code suffix returnPc))
        Configuration.halted 1 middle.1 = PMF.pure ({middle.1 with halted := true}, 1) := by
    have hLogical := (P.invocation pre suffix returnPc layout).result_support input middle hMiddle
    have hReturn := SubroutineContract.call_returns P.procedure pre suffix returnPc layout
      P.closed P.entry P.active P.halted input middle.1 hLogical
    simp [runToBoundary, hReturn.2.1, stepPMF, next, hReturn.1, lookup, Instruction.next,
      PMF.pure_bind, PMF.pure_map]
  have h := P.invocation_firstHalt_compose pre suffix returnPc layout input 1 (by
    intro middle hMiddle result hResult
    rw [hOne middle hMiddle, PMF.mem_support_pure_iff] at hResult
    subst result
    rfl)
  rw [h]
  rw [PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext middle hMiddle
  rw [hOne middle hMiddle, PMF.pure_map]
  rfl

end Machine.NativeComponent
