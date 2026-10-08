import Foundation.Crypto.Semantics.Machine.NativeCompositionContract
import Foundation.Crypto.Semantics.Machine.NativeObservers
import Foundation.Crypto.Semantics.Machine.ControlClosure

/-! A genuinely randomized native stage followed by deterministic native
observation, compiled to one fixed program. Complete tape layouts and the
uniform result distribution are proved for arbitrary inherited tapes. -/
namespace Foundation.Examples.NativeCompositionContract
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

private theorem random_closed (start next : Configuration) (hp : start.pc < NativeObservers.randomCode.length)
    (hs : Step NativeObservers.randomCode start next) (ha : next.halted = false) :
    next.pc < NativeObservers.randomCode.length := by
  exact Program.controlClosed_step (code := NativeObservers.randomCode) (by decide) start next hp hs ha

private theorem first_closed (start next : Configuration) (hp : start.pc < NativeObservers.firstCode.length)
    (hs : Step NativeObservers.firstCode start next) (ha : next.halted = false) :
    next.pc < NativeObservers.firstCode.length := by
  exact Program.controlClosed_step (code := NativeObservers.firstCode) (by decide) start next hp hs ha

noncomputable def native :=
  Machine.NativeCompositionContract.native NativeObservers.random NativeObservers.first
    random_closed (fun _ => by change 0 < 2; decide) (fun _ => rfl) NativeObservers.random_halted
    first_closed (fun _ => rfl) (by decide) NativeObservers.first_halted
    (fun _ => 3) (fun _ _ _ => Nat.le_refl _)

def finish (machine : Configuration) (bit : Bool) : Configuration :=
  {machine with pc := 9, outputTape := machine.outputTape.write (some bit), halted := true}

theorem code : native.code = NativeObservers.randomCode.followedBy NativeObservers.firstCode := rfl

theorem code_length : native.code.length = 10 := by
  exact Machine.NativeCompositionContract.code_length NativeObservers.random NativeObservers.first

theorem budget (machine : Configuration) : native.execution.budget machine = 6 := rfl

theorem semantics (machine : Configuration) :
    native.execution.semantics machine = sampleBit.map (finish machine) := by
  rw [native, Machine.NativeCompositionContract.semantics]
  simp only [NativeObservers.random, NativeObservers.first, Machine.Procedure.ofFixed,
    TimedExecution.Procedure.ofFixed, PMF.bind_map, Function.comp_def, PMF.pure_map]
  congr 1

theorem run (machine : Configuration) (horizon : Nat) (hTime : 6 ≤ horizon) :
    evalConfigWithin native.code (machine.resumeAt 0) horizon = sampleBit.map (finish machine) := by
  have h := Machine.NativeCompositionContract.run NativeObservers.random NativeObservers.first
    random_closed (fun _ => by change 0 < 2; decide) (fun _ => rfl) NativeObservers.random_halted
    first_closed (fun _ => rfl) (by decide) NativeObservers.first_halted
    (fun _ => 3) (fun _ _ _ => Nat.le_refl _) machine horizon hTime
  exact h.trans (semantics machine)

theorem input_preserved (machine : Configuration) (target : Configuration)
    (h : target ∈ (native.execution.semantics machine).support) : target.inputTape = machine.inputTape := by
  rw [semantics, PMF.mem_support_map_iff] at h
  obtain ⟨bit, _, rfl⟩ := h
  rfl

end Foundation.Examples.NativeCompositionContract
