import Foundation.Crypto.Semantics.Machine.MaskingFused

/-! Eliminate explicit halts appended by compiler passes. The machine already
halts on falling off the source program, so every retained-state transition
is identical, including jumps into the appended position and all random
choices. Both the legacy and fused controllers satisfy this exact equality. -/
namespace Machine.Masking
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

def appendHalt : Code → Code
  | .native program => .native (program ++ [.halt])
  | .masked side program => .masked side (program ++ [.halt])

theorem initial_appendHalt (code : Code) (header left right challenge : List Bool) :
    initial (appendHalt code) header left right challenge = initial code header left right challenge := by
  cases code <;> rfl

theorem step_appendHalt (code : Code) (config : Configuration) :
    step (appendHalt code) config = step code config := by
  cases config <;> cases code <;> simp only [step, appendHalt, Code.program, Machine.stepPMF_append_halt]

theorem eval_appendHalt (code : Code) (config : Configuration) (fuel : Nat) :
    eval (appendHalt code) config fuel = eval code config fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [eval, ih]
      congr 1
      funext config
      exact step_appendHalt code config

namespace Fused

theorem step_appendHalt (code : Code) (config : Configuration) :
    step (appendHalt code) config = step code config := by
  cases config with
  | «prefix» header mask challenge acc => simpa only [step] using Masking.step_appendHalt code (.prefix header mask challenge acc)
  | masking mask challenge acc =>
      simpa only [step] using Masking.step_appendHalt code (.masking mask challenge acc)
  | running machine =>
      simpa only [step] using Masking.step_appendHalt code (.running machine)
  | loading acc tape =>
      cases acc with
      | nil => simpa only [step] using Masking.step_appendHalt code (.loading [] tape)
      | cons bit rest =>
          cases rest with
          | nil => rfl
          | cons next tail =>
              simpa only [step] using Masking.step_appendHalt code (.loading (bit :: next :: tail) tape)

theorem eval_appendHalt (code : Code) (config : Configuration) (fuel : Nat) :
    eval (appendHalt code) config fuel = eval code config fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [eval, ih]
      congr 1
      funext config
      exact step_appendHalt code config

end Fused
end Machine.Masking
