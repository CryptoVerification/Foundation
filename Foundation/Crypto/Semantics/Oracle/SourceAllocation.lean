import Foundation.Crypto.Semantics.Oracle.ControllerStorage

/-! Explicit allocation allowance at public-controller copying transitions.
Bulk request copies and oracle-returned data are charged, rather than hidden
inside a constant per-instruction storage growth bound. -/
namespace CryptoOracle.Interactive.SourceAllocation
open Foundation.Probability
universe u

def allowance (stateIncrement responseCap : Nat) : Control → Nat
  | .running machine => machine.outputTape.cells
  | .awaiting _ request => stateIncrement + request.length + 2 * responseCap
  | _ => 0

variable {State : Type u}

theorem step_bound (stateSize : State → Nat) (code : Code) (oracle : BitOracle State)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start next : Configuration State)
    (h : next ∈ (Reification.timedStep code oracle start).support) :
    SourceStorage.cells stateSize next ≤ SourceStorage.cells stateSize start +
      allowance stateIncrement responseCap start.control + 2 := by
  rcases start with ⟨state, control, trace⟩
  cases control with
  | running machine =>
      cases hh : machine.halted with
      | true =>
          simp [Reification.timedStep, Reification.terminal, hh] at h
          subst next
          simp [allowance] <;> omega
      | false =>
          cases hi : code[machine.pc]? with
          | none =>
              simp [Reification.timedStep, Reification.terminal, Reification.perform,
                Reification.action, transition, hh, hi] at h
              subst next
              simp [SourceStorage.cells, SourceStorage.controlCells, allowance]
              omega
          | some instruction =>
              cases instruction with
              | call =>
                  simp [Reification.timedStep, Reification.terminal, Reification.perform,
                    Reification.action, transition, hh, hi] at h
                  subst next
                  simp [SourceStorage.cells, SourceStorage.controlCells, allowance,
                    Machine.Configuration.advance, Machine.Configuration.tapeCells] <;> omega
              | native instruction =>
                  cases hn : instruction.next machine with
                  | inl target =>
                      have hb := Machine.tapeCells_le_of_instruction instruction machine target (by simp [hn])
                      simp [Reification.timedStep, Reification.terminal, Reification.perform,
                        Reification.action, transition, hh, hi, hn] at h
                      subst next
                      simp only [SourceStorage.cells, SourceStorage.controlCells, allowance]
                      omega
                  | inr pair =>
                      rcases pair with ⟨zero, one⟩
                      have hz := Machine.tapeCells_le_of_instruction instruction machine zero (by simp [hn])
                      have ho := Machine.tapeCells_le_of_instruction instruction machine one (by simp [hn])
                      simp only [Reification.timedStep, Reification.terminal, hh, Bool.false_eq_true,
                        ↓reduceIte, Reification.perform, Reification.action, transition, hi, hn,
                        PMF.mem_support_map_iff] at h
                      obtain ⟨bit, _, he⟩ := h
                      subst next
                      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte,
                        SourceStorage.cells, SourceStorage.controlCells, allowance] <;> omega
  | sending machine tape reversed =>
      cases ht : tape.current <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition, ht] at h <;> subst next
      · simp [SourceStorage.cells, SourceStorage.controlCells, allowance]
        omega
      · have hb := Machine.Tape.cells_moveRight_le tape
        simp only [SourceStorage.cells, SourceStorage.controlCells, allowance, List.length_cons]
        omega
  | reversing machine remaining request =>
      cases remaining <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition] at h <;> subst next <;>
        simp [SourceStorage.cells, SourceStorage.controlCells, allowance] <;> omega
  | awaiting machine request =>
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, PMF.mem_support_map_iff] at h
      obtain ⟨result, hr, he⟩ := h
      subst next
      obtain ⟨hs, hl⟩ := hOracle state request result hr
      simp only [SourceStorage.cells, SourceStorage.controlCells, SourceStorage.traceCells,
        allowance, Machine.Tape.cells, List.length_nil]
      omega
  | loading machine remaining tape =>
      cases remaining <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition] at h <;> subst next <;>
        simp [SourceStorage.cells, SourceStorage.controlCells, allowance, Machine.Tape.cells_write] <;> omega
  | advancing machine remaining tape =>
      simp [Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition] at h
      subst next
      have hb := Machine.Tape.cells_moveRight_le tape
      simp only [SourceStorage.cells, SourceStorage.controlCells, allowance]
      omega
  | rewinding machine tape =>
      cases hl : tape.left <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition, hl] at h <;> subst next
      · simp [SourceStorage.cells, SourceStorage.controlCells, allowance, Machine.Configuration.tapeCells]
        omega
      · have hb := Machine.Tape.cells_moveLeft_le tape
        simp only [SourceStorage.cells, SourceStorage.controlCells, allowance]
        omega
  | finished bit =>
      simp [Reification.timedStep, Reification.terminal] at h
      subst next
      omega

end CryptoOracle.Interactive.SourceAllocation
