import Foundation.Crypto.Semantics.Machine.NativeFixedComponent
import Foundation.Crypto.Semantics.Machine.NativeFirstArrival

/-! Package an arbitrary terminating native program as a closed component.
Source jumps may leave the source list, and the list may be empty. The
existing relocation redirects such jumps to explicit native return code.
Both tapes and their entire finite representations are preserved. A bound
of two extra transitions suffices; this is not an exact time translation. -/
namespace Machine.NativeHaltingProgram
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

def code (source : Program) : Program := source.followedBy [.halt]

theorem code_length (source : Program) : (code source).length = source.length + 4 := by
  simp [code, Program.followedBy]

def finish (source : Program) (state : Configuration) : Configuration :=
  {state with pc := source.length + 3, halted := true}

private theorem halt_run (state : Configuration) :
    evalConfigWithin [.halt] (state.resumeAt 0) 1 = PMF.pure {state.resumeAt 0 with halted := true} := by
  simp [evalConfigWithin, stepPMF, next, Instruction.next, Configuration.resumeAt]

theorem run (source : Program) (start : Configuration) (hPc : start.pc = 0)
    (hActive : start.halted = false) (limit : Nat)
    (halts : ∀ state ∈ (evalConfigWithin source start limit).support, state.halted = true) :
    evalConfigWithin (code source) start (limit + 2) =
      (evalConfigWithin source start limit).map (finish source) := by
  have h := Program.evalConfigWithin_twoStages_configuration source [.halt] start hPc hActive limit 1
    (fun state hRun => halts state ((mem_support_evalConfigWithin_iff _ _ _ _).mpr hRun))
    (by
      intro state _ target hRun
      have hTarget := (mem_support_evalConfigWithin_iff [.halt] (state.resumeAt 0) target 1).mpr hRun
      rw [halt_run, PMF.mem_support_pure_iff] at hTarget
      subst target
      rfl)
  dsimp only at h
  simp only [Program.asSubroutine_length, List.length_singleton] at h
  change evalConfigWithin (code source) start (limit + (1 + 1)) = _ at h
  rw [h]
  simp only [halt_run, PMF.pure_map]
  rfl

/-- No source control-closure certificate is needed. The transformed
program's closure and every input's successful halt are proved separately. -/
noncomputable def component {Input : Type u} (source : Program)
    (entry : Input → Configuration) (limit : Input → Nat)
    (entryPc : ∀ input, (entry input).pc = 0)
    (entryActive : ∀ input, (entry input).halted = false)
    (halts : ∀ input, ∀ state ∈ (evalConfigWithin source (entry input) (limit input)).support, state.halted = true) :
    NativeComponent Input Configuration where
  procedure := Machine.Procedure.ofFixed (code source) entry (fun _ => finish source)
    (fun input => evalConfigWithin source (entry input) (limit input)) (fun input => limit input + 2)
    (fun input => run source (entry input) (entryPc input) (entryActive input) (limit input) (halts input))
  closed := Program.followedBy_control_closed source [.halt]
  entry := by intro input; change (entry input).pc < (code source).length; rw [entryPc, code_length]; omega
  active := entryActive
  halted := fun _ _ _ => rfl

theorem component_budget {Input : Type u} (source : Program) (entry : Input → Configuration)
    (limit : Input → Nat) (entryPc entryActive halts) (input : Input) :
    (component source entry limit entryPc entryActive halts).procedure.execution.budget input = limit input + 2 := rfl

theorem component_exit_tapes {Input : Type u} (source : Program) (entry : Input → Configuration)
    (limit : Input → Nat) (entryPc entryActive halts) (input : Input) (state : Configuration) :
    let output := (component source entry limit entryPc entryActive halts).procedure.execution.exit input state
    output.inputTape = state.inputTape ∧ output.outputTape = state.outputTape := ⟨rfl, rfl⟩

end Machine.NativeHaltingProgram
