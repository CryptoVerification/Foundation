import Foundation.Crypto.Semantics.ExactClockTransport
import Foundation.Crypto.Semantics.Machine.NativeExactClock
import Foundation.Crypto.Semantics.Machine.TapeSwapProcedure

/-! Transfer exact clocks to code with exchanged tape operands. This
compiles relabeled instructions and does not perform a runtime tape swap. -/
namespace Machine
open Foundation.Probability TimedExecution

def Configuration.swapTapesEquiv : Configuration ≃ Configuration where
  toFun := Configuration.swapTapes
  invFun := Configuration.swapTapes
  left_inv := Configuration.swapTapes_swapTapes
  right_inv := Configuration.swapTapes_swapTapes

noncomputable def swapTapesExactClock {code : Program}
    (clock : ExactBoundaryClock (stepPMF code) Configuration.halted) :
    ExactBoundaryClock (stepPMF code.swapTapes) Configuration.halted :=
  clock.transport Configuration.swapTapesEquiv (stepPMF code.swapTapes) Configuration.halted
    (fun _ => rfl) (stepPMF_swapTapes code)

@[simp] theorem swapTapesExactClock_remaining {code : Program}
    (clock : ExactBoundaryClock (stepPMF code) Configuration.halted) (state : Configuration) :
    (swapTapesExactClock clock).remaining state.swapTapes = clock.remaining state := rfl

@[simp] theorem swapTapesExactClock_valid {code : Program}
    (clock : ExactBoundaryClock (stepPMF code) Configuration.halted) (state : Configuration) :
    (swapTapesExactClock clock).valid state.swapTapes ↔ clock.valid state := Iff.rfl

end Machine
