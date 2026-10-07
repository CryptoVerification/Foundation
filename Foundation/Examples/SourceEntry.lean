import Foundation.Crypto.Semantics.Oracle.SourceEntry
import Foundation.Crypto.Semantics.Machine.PreparedXor
import Foundation.Examples.PreparedCallback

/-! A real call instruction with a physical plaintext request enters the
common preparation controller. Source input, PC advancement, state and
history remain explicit. No external query substitutes for native handling. -/
namespace Foundation.SourceEntryExamples
open Foundation.Probability TimedExecution Foundation.Symmetric
open CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

def code : Code := [.call, .native .halt]

def machine (input : Machine.Tape) (request : List Bool) (tail : List (Option Bool)) : Machine.Configuration :=
  { inputTape := input, outputTape := RequestExport.packetTape [] tail request }

theorem entry {State : Type u} (width : Nat) (key message : Bits width)
    (keyTail messageTail : List (Option Bool)) (input : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool)) (oracle : BitOracle State) :
    TimedExecution.eval (SourceEntry.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) (2 * width + 4)
      (.source (Machine.PairPreparation.operand [] key.toList keyTail)
        ⟨state, .running (machine input message.toList messageTail), trace⟩) =
      PMF.pure (.handling (machine input message.toList messageTail).advance state trace message.toList
        (.preparing (Machine.PairPreparation.procedure.entry
          (PreparedCallbackExamples.operands key message keyTail messageTail)))) := by
  have h := SourceEntry.call_entry Machine.OneTimePad.Prepared.listProcedure.code code oracle
    (Machine.PairPreparation.operand [] key.toList keyTail) (machine input message.toList messageTail)
    state trace message.toList [] messageTail rfl rfl rfl
  simpa only [Bits.length_toList, PreparedCallbackExamples.operands, Machine.PairPreparation.procedure,
    Procedure.ofFixed, machine, RequestExport.packetTape, Machine.PairPreparation.operand,
    Machine.PairPreparation.fromCells, List.reverse_nil, List.map_nil] using h

end Foundation.SourceEntryExamples
