import Foundation.Crypto.Semantics.Machine.NativeComponent
import Foundation.Crypto.Semantics.Machine.ControlClosure

/-! Reuse existing whole-program distribution proofs as native components.
The constructor does not infer termination, prepare tapes, or turn a fixed
horizon into a claim about actual first-arrival costs. Linked calls retain
their actual first-return times through the existing boundary construction. -/
namespace Machine.NativeComponent
open Foundation.Probability
universe u v

noncomputable def ofFixed {Input : Type u} {Output : Type v} (code : Program)
    (entry : Input → Configuration) (exit : Input → Output → Configuration)
    (semantics : Input → PMF Output) (duration : Input → Nat)
    (run : ∀ input, evalConfigWithin code (entry input) (duration input) = (semantics input).map (exit input))
    (closed : code.ControlClosed) (inside : ∀ input, (entry input).pc < code.length)
    (active : ∀ input, (entry input).halted = false)
    (halted : ∀ input output, output ∈ (semantics input).support → (exit input output).halted = true) :
    NativeComponent Input Output where
  procedure := Machine.Procedure.ofFixed code entry exit semantics duration run
  closed := Program.controlClosed_step closed
  entry := inside
  active := active
  halted := halted

end Machine.NativeComponent
