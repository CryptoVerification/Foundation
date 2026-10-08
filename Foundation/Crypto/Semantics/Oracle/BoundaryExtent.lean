import Foundation.Crypto.Semantics.Oracle.ControllerExtent
import Foundation.Crypto.Semantics.Oracle.ResponseLoading

/-! Value-independent size rules for loaded responses, retained private
operands and transcript extension. These count the represented delimiter. -/
namespace CryptoOracle.Interactive.ResponseLoading

theorem loaded_cells (response : List Bool) :
    (loaded response).cells = response.length + 1 := by
  cases response with
  | nil => rfl
  | cons bit rest => simp [loaded, fromCells, Machine.Tape.cells]; omega

end CryptoOracle.Interactive.ResponseLoading

namespace Machine.PairPreparation

theorem operand_cells (past remaining : List Bool) (tail : List (Option Bool)) :
    (operand past remaining tail).cells = past.length + remaining.length + tail.length + 1 := by
  cases remaining <;> simp [operand, fromCells, Tape.cells] <;> omega

end Machine.PairPreparation

namespace CryptoOracle.Interactive.ControllerExtent

/-- Appending an interaction grows the prior extent by at most one, apart
from the new request and response themselves. No bound on their values is used. -/
theorem trace_cons_bound (request response : List Bool) (trace : List (List Bool × List Bool)) :
    traceExtent ((request, response) :: trace) ≤
      max request.length (max response.length (traceExtent trace + 1)) := by
  have h := trace_length trace
  simp only [traceExtent]
  omega

end CryptoOracle.Interactive.ControllerExtent
