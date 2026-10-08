import Foundation.Crypto.Semantics.Oracle.SourcePrefix
import Foundation.Crypto.Semantics.Machine.Storage

/-! Retained data in the source controller before its first query.
Every stored tape copy and temporary bit list is counted. Transcript data
and a client-supplied size for the opaque oracle state are counted too.
Finite code and control-address encodings are separate resources. -/
namespace CryptoOracle.Interactive.SourceStorage
open Foundation.Probability
universe u

def controlCells : Control → Nat
  | .running machine => machine.tapeCells
  | .sending machine tape reversed => machine.tapeCells + tape.cells + reversed.length
  | .reversing machine remaining request => machine.tapeCells + remaining.length + request.length
  | .awaiting machine request => machine.tapeCells + request.length
  | .loading machine remaining tape => machine.tapeCells + remaining.length + tape.cells
  | .advancing machine remaining tape => machine.tapeCells + remaining.length + tape.cells
  | .rewinding machine tape => machine.tapeCells + tape.cells
  | .finished _ => 1

def traceCells : List (List Bool × List Bool) → Nat
  | [] => 0
  | (request, response) :: rest => request.length + response.length + traceCells rest

def cells {State : Type u} (stateSize : State → Nat) (frame : Configuration State) : Nat :=
  stateSize frame.state + controlCells frame.control + traceCells frame.reverseTrace

/-- Only these phases are reachable before the first query. -/
def requestPhase : Control → Prop
  | .running _ | .sending _ _ _ | .reversing _ _ _ | .awaiting _ _ | .finished _ => True
  | _ => False

/-- Reserve space for the real output-tape copy made by the call instruction.
The reservation is an analysis measure, not additional physical storage. -/
def capacity : Control → Nat
  | .running machine => 2 * machine.tapeCells
  | other => controlCells other

theorem cells_le_capacity (control : Control) : controlCells control ≤ capacity control := by
  cases control <;> simp [controlCells, capacity]
  omega

def potential {State : Type u} (stateSize : State → Nat) (frame : Configuration State) : Nat :=
  stateSize frame.state + capacity frame.control + traceCells frame.reverseTrace

theorem local_bound {State : Type u} (stateSize : State → Nat)
    (code : Code) (oracle : BitOracle State) (start next : Configuration State)
    (hValid : requestPhase start.control)
    (h : next ∈ (SourcePrefix.step code oracle start).support) :
    requestPhase next.control ∧ potential stateSize next ≤ potential stateSize start + 2 := by
  rcases start with ⟨state, control, trace⟩
  cases control with
  | running machine =>
      cases hh : machine.halted with
      | true =>
          simp [SourcePrefix.step, SourcePrefix.boundary, Reification.terminal, hh] at h
          subst next
          exact ⟨trivial, by omega⟩
      | false =>
          cases hi : code[machine.pc]? with
          | none =>
              simp [SourcePrefix.step, SourcePrefix.boundary, Reification.terminal,
                Reification.timedStep, Reification.perform, Reification.action, transition, hh, hi] at h
              subst next
              simp [requestPhase, potential, capacity, controlCells]
              omega
          | some instruction =>
              cases instruction with
              | call =>
                  simp [SourcePrefix.step, SourcePrefix.boundary, Reification.terminal,
                    Reification.timedStep, Reification.perform, Reification.action, transition, hh, hi] at h
                  subst next
                  simp [requestPhase, potential, capacity, controlCells,
                    Machine.Configuration.advance, Machine.Configuration.tapeCells]
                  omega
              | native instruction =>
                  cases hn : instruction.next machine with
                  | inl target =>
                      have hb := Machine.tapeCells_le_of_instruction instruction machine target (by simp [hn])
                      simp [SourcePrefix.step, SourcePrefix.boundary, Reification.terminal,
                        Reification.timedStep, Reification.perform, Reification.action, transition, hh, hi, hn] at h
                      subst next
                      refine ⟨trivial, ?_⟩
                      simp only [potential, capacity]
                      omega
                  | inr pair =>
                      rcases pair with ⟨zero, one⟩
                      simp only [SourcePrefix.step, SourcePrefix.boundary, Reification.terminal, hh,
                        Bool.false_eq_true, ↓reduceIte, Reification.timedStep, Reification.perform,
                        Reification.action, transition, hi, hn, PMF.mem_support_map_iff] at h
                      obtain ⟨bit, _, he⟩ := h
                      subst next
                      have hz := Machine.tapeCells_le_of_instruction instruction machine zero (by simp [hn])
                      have ho := Machine.tapeCells_le_of_instruction instruction machine one (by simp [hn])
                      cases bit <;> refine ⟨trivial, ?_⟩ <;> simp only [potential, capacity, Bool.false_eq_true,
                        ↓reduceIte] <;> omega
  | sending machine tape reversed =>
      cases ht : tape.current <;>
        simp [SourcePrefix.step, SourcePrefix.boundary, Reification.terminal,
          Reification.timedStep, Reification.perform, Reification.action, transition, ht] at h <;> subst next
      · simp [requestPhase, potential, capacity, controlCells]
        omega
      · have hb := Machine.Tape.cells_moveRight_le tape
        refine ⟨trivial, ?_⟩
        simp only [potential, capacity, controlCells, List.length_cons]
        omega
  | reversing machine remaining request =>
      cases remaining <;>
        simp [SourcePrefix.step, SourcePrefix.boundary, Reification.terminal,
          Reification.timedStep, Reification.perform, Reification.action, transition] at h <;> subst next <;>
        simp [requestPhase, potential, capacity, controlCells]
      all_goals omega
  | awaiting machine request =>
      simp [SourcePrefix.step, SourcePrefix.boundary] at h
      subst next
      exact ⟨trivial, by omega⟩
  | finished bit =>
      simp [SourcePrefix.step, SourcePrefix.boundary, Reification.terminal] at h
      subst next
      exact ⟨trivial, by omega⟩
  | loading machine remaining tape => exact False.elim hValid
  | advancing machine remaining tape => exact False.elim hValid
  | rewinding machine tape => exact False.elim hValid

theorem peak {State : Type u} (stateSize : State → Nat) (code : Code)
    (oracle : BitOracle State) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : Configuration State) (hValid : requestPhase start.control)
    (h : intermediate ∈ (TimedExecution.eval (SourcePrefix.step code oracle) elapsed start).support) :
    cells stateSize intermediate ≤ potential stateSize start + 2 * horizon := by
  have hb := TimedExecution.ResourceGrowth.invariant_endpoint (SourcePrefix.step code oracle)
    (potential stateSize) (fun frame => requestPhase frame.control) 2
    (fun start hv next hn => local_bound stateSize code oracle start next hv hn) elapsed start intermediate hValid h
  have hc := cells_le_capacity intermediate.control
  simp only [cells, potential] at *
  omega

theorem running_peak {State : Type u} (stateSize : State → Nat) (code : Code)
    (oracle : BitOracle State) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (machine : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (intermediate : Configuration State)
    (h : intermediate ∈ (TimedExecution.eval (SourcePrefix.step code oracle) elapsed
      ⟨state, .running machine, trace⟩).support) :
    cells stateSize intermediate ≤ stateSize state + 2 * machine.tapeCells + traceCells trace + 2 * horizon :=
  peak stateSize code oracle horizon elapsed hElapsed ⟨state, .running machine, trace⟩ intermediate trivial h

/-- Includes the unchanged private key of the actual one-use controller.
The boundary endpoint is charged its actual first-arrival cost. -/
theorem procedure_endpoint {State : Type u} (stateSize : State → Nat) (code : Code)
    (oracle : BitOracle State) (native : Machine.Program) (key : Machine.Tape)
    (input : SourcePrefix.Input code oracle) (hValid : requestPhase input.start.control)
    (result : Configuration State × Nat)
    (h : result ∈ ((SourcePrefix.procedure code oracle native key).costed input).support) :
    key.cells + cells stateSize result.1 ≤
      key.cells + potential stateSize input.start + 2 * result.2 := by
  change result ∈ ((TimedExecution.runToBoundary (SourcePrefix.step code oracle)
    SourcePrefix.boundary input.budget input.start).map id).support at h
  rw [PMF.map_id] at h
  have hb := TimedExecution.ResourceGrowth.invariant_boundary_endpoint (SourcePrefix.step code oracle)
    (potential stateSize) (fun frame => requestPhase frame.control) 2
    (fun start hv next hn => local_bound stateSize code oracle start next hv hn)
    SourcePrefix.boundary input.budget input.start result hValid h
  have hc := cells_le_capacity result.1.control
  simp only [cells, potential] at *
  omega

end CryptoOracle.Interactive.SourceStorage
