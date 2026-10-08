import Foundation.Crypto.Semantics.Oracle.FailureCallback

/-! Both preparation outcomes use physical tagged responses. Successful
native output is exported, tagged cell by cell, exported again and loaded.
The suspended caller metadata is supplied by the surrounding source control. -/
namespace CryptoOracle.Interactive.CheckedCallback
open Foundation.Probability
universe u

inductive Control (State : Type u) where
  | preparing (preparation : Machine.PreparationCheck.Control)
  | computing (first second : Machine.Tape) (component : Machine.ResponseExport.Control)
  | tagging (first second : Machine.Tape) (packet : Machine.ResponsePacket.Control)
  | calling (first second : Machine.Tape) (callback : NativeCallback.Control State)

noncomputable def step {State : Type u} (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) : Control State → PMF (Control State)
  | .preparing (.preparing (.ready first second buffer)) =>
      PMF.pure (.computing first second (.running { inputTape := buffer }))
  | .preparing (.failure (.returned first second response)) =>
      PMF.pure (.calling first second (.responding (.running { outputTape := response, halted := true })))
  | .preparing preparation => (Machine.PreparationCheck.step preparation).map .preparing
  | .computing first second (.returned payload) =>
      PMF.pure (.tagging first second (.start (some payload)))
  | .computing first second component =>
      (Machine.ResponseExport.step native component).map (.computing first second)
  | .tagging first second (.returned response) =>
      PMF.pure (.calling first second (.responding (.running { outputTape := response, halted := true })))
  | .tagging first second packet => (Machine.ResponsePacket.step packet).map (.tagging first second)
  | .calling first second callback =>
      (NativeCallback.step [] code oracle machine state trace request callback).map (.calling first second)

end CryptoOracle.Interactive.CheckedCallback
