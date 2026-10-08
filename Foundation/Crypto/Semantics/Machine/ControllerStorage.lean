import Foundation.Crypto.Semantics.Machine.Storage
import Foundation.Crypto.Semantics.Machine.PreparationCheck
import Foundation.Crypto.Semantics.Machine.PrivateInitialization

/-! Retained cells of the physical preparation and response controllers.
Every stored tape and temporary list is counted, including blanks. Native
code, addresses, and outer caller/oracle storage are separate resources. -/
namespace Machine.ControllerStorage
open Foundation.Probability TimedExecution

set_option maxHeartbeats 1000000

def pairCells : PairPreparation.Control → Nat
  | .reading a b c | .advancingSecond a b c
  | .advancingKey a b c | .advancingMessage a b c | .checkingEnd a b c
  | .rewinding a b c | .ready a b c | .rejected a b c => a.cells + b.cells + c.cells
  | .checking _ a b c | .advancingFirst _ a b c | .writingSecond _ a b c =>
      a.cells + b.cells + c.cells + 1
  | .writingFirst _ _ a b c => a.cells + b.cells + c.cells + 2

def packetCells : ResponsePacket.Control → Nat
  | .start response => (response.getD []).length
  | .writing remaining tape | .advancing remaining tape => remaining.length + tape.cells
  | .returned tape => tape.cells

def failureCells : PreparationFailure.Control → Nat
  | .detected a b c => a.cells + b.cells + c.cells
  | .restoring preparation => pairCells preparation
  | .writing a b packet => a.cells + b.cells + packetCells packet
  | .returned a b c => a.cells + b.cells + c.cells

def checkCells : PreparationCheck.Control → Nat
  | .preparing preparation => pairCells preparation
  | .failure recovery => failureCells recovery

def exportCells : ResponseExport.Control → Nat
  | .running machine => machine.tapeCells
  | .rewinding tape => tape.cells
  | .collecting tape reversed => tape.cells + reversed.length
  | .reversing remaining packet => remaining.length + packet.length
  | .returned packet => packet.length

def initializationCells : PrivateInitialization.Control → Nat
  | .generating machine => machine.tapeCells
  | .rewinding tape | .ready tape => tape.cells

theorem pair_local (start next : PairPreparation.Control)
    (h : next ∈ (PairPreparation.step start).support) : pairCells next ≤ pairCells start + 1 := by
  cases start
  all_goals rename_i a b c
  all_goals have hal := Tape.cells_moveLeft_le a
  all_goals have hbl := Tape.cells_moveLeft_le b
  all_goals have hcl := Tape.cells_moveLeft_le c
  all_goals have har := Tape.cells_moveRight_le a
  all_goals have hbr := Tape.cells_moveRight_le b
  all_goals have hcr := Tape.cells_moveRight_le c
  all_goals simp only [PairPreparation.step] at h
  all_goals repeat' first
    | split at h
    | (rw [PMF.mem_support_pure_iff] at h; subst next)
  all_goals simp_all only [pairCells, Tape.cells_write]
  all_goals omega

theorem packet_local (start next : ResponsePacket.Control)
    (h : next ∈ (ResponsePacket.step start).support) : packetCells next ≤ packetCells start + 1 := by
  cases start with
  | start response =>
      cases response <;> simp [ResponsePacket.step, PMF.mem_support_pure_iff] at h <;> subst next <;>
        simp [packetCells, Tape.cells, Tape.write]
  | writing remaining tape =>
      cases remaining <;> simp [ResponsePacket.step, PMF.mem_support_pure_iff] at h <;> subst next <;>
        simp [packetCells, Tape.cells_write] <;> omega
  | advancing remaining tape =>
      simp [ResponsePacket.step, PMF.mem_support_pure_iff] at h
      subst next
      have hb := Tape.cells_moveRight_le tape
      simp only [packetCells]
      omega
  | returned tape =>
      simp [ResponsePacket.step, PMF.mem_support_pure_iff] at h
      subst next
      omega

theorem failure_local (start next : PreparationFailure.Control)
    (h : next ∈ (PreparationFailure.step start).support) : failureCells next ≤ failureCells start + 1 := by
  cases start with
  | detected a b c =>
      simp [PreparationFailure.step, PMF.mem_support_pure_iff] at h
      subst next
      simp [failureCells, pairCells]
  | restoring preparation =>
      cases preparation <;> simp only [PreparationFailure.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           exact pair_local _ value hv)
        | (rw [PMF.mem_support_pure_iff] at h; subst next
           simp [failureCells, pairCells, packetCells] <;> omega)
  | writing a b packet =>
      cases packet <;> simp only [PreparationFailure.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           have hb := packet_local _ value hv
           simp only [failureCells] at *
           omega)
        | (rw [PMF.mem_support_pure_iff] at h; subst next
           simp [failureCells, packetCells])
  | returned a b c =>
      simp [PreparationFailure.step, PMF.mem_support_pure_iff] at h
      subst next
      omega

theorem check_local (start next : PreparationCheck.Control)
    (h : next ∈ (PreparationCheck.step start).support) : checkCells next ≤ checkCells start + 1 := by
  cases start with
  | preparing preparation =>
      cases preparation <;> simp only [PreparationCheck.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h
           obtain ⟨value, hv, he⟩ := h
           subst next
           exact pair_local _ value hv)
        | (rw [PMF.mem_support_pure_iff] at h; subst next
           simp [checkCells, failureCells, pairCells])
  | failure recovery =>
      rw [PreparationCheck.step, PMF.mem_support_map_iff] at h
      obtain ⟨value, hv, he⟩ := h
      subst next
      exact failure_local recovery value hv

theorem export_local (code : Program) (start next : ResponseExport.Control)
    (h : next ∈ (ResponseExport.step code start).support) : exportCells next ≤ exportCells start + 2 := by
  cases start with
  | running machine =>
      by_cases hh : machine.halted = true
      · simp [ResponseExport.step, hh, PMF.mem_support_pure_iff] at h
        subst next
        simp [exportCells, Configuration.tapeCells] <;> omega
      · simp only [ResponseExport.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨value, hv, he⟩ := h
        subst next
        have hb := tapeCells_le_of_support code machine value hv
        simp only [exportCells]
        omega
  | rewinding tape =>
      cases hl : tape.left <;> simp [ResponseExport.step, hl, PMF.mem_support_pure_iff] at h <;> subst next
      · simp [exportCells] <;> omega
      · have hb := Tape.cells_moveLeft_le tape
        simp only [exportCells]
        omega
  | collecting tape reversed =>
      cases hc : tape.current <;> simp [ResponseExport.step, hc, PMF.mem_support_pure_iff] at h <;> subst next
      · simp [exportCells] <;> omega
      · have hb := Tape.cells_moveRight_le tape
        simp only [exportCells, List.length_cons]
        omega
  | reversing remaining packet =>
      cases remaining <;> simp [ResponseExport.step, PMF.mem_support_pure_iff] at h <;> subst next <;>
        simp [exportCells] <;> omega
  | returned packet =>
      simp [ResponseExport.step, PMF.mem_support_pure_iff] at h
      subst next
      omega

/-- The common native exporter retains all its tapes and temporary lists.
The bound holds at every supported prefix and for every native program. -/
theorem export_peak (code : Program) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : ResponseExport.Control)
    (h : intermediate ∈ (eval (ResponseExport.step code) elapsed start).support) :
    exportCells intermediate ≤ exportCells start + 2 * horizon := by
  have hb := ResourceGrowth.prefix_bound (ResponseExport.step code) exportCells 2
    (export_local code) horizon elapsed hElapsed start intermediate h
  omega

theorem check_peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : PreparationCheck.Control)
    (h : intermediate ∈ (eval PreparationCheck.step elapsed start).support) :
    checkCells intermediate ≤ checkCells start + horizon := by
  simpa using ResourceGrowth.prefix_bound PreparationCheck.step checkCells 1
    check_local horizon elapsed hElapsed start intermediate h

theorem initialization_local (code : Program) (start next : PrivateInitialization.Control)
    (h : next ∈ (PrivateInitialization.step code start).support) :
    initializationCells next ≤ initializationCells start + 1 := by
  cases start with
  | generating machine =>
      by_cases hh : machine.halted = true
      · simp [PrivateInitialization.step, hh, PMF.mem_support_pure_iff] at h
        subst next
        simp [initializationCells, Configuration.tapeCells] <;> omega
      · simp only [PrivateInitialization.step, hh, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_map_iff] at h
        obtain ⟨value, hv, he⟩ := h
        subst next
        exact tapeCells_le_of_support code machine value hv
  | rewinding tape =>
      cases hl : tape.left <;> simp [PrivateInitialization.step, hl, PMF.mem_support_pure_iff] at h <;> subst next
      · simp [initializationCells]
      · exact Tape.cells_moveLeft_le tape
  | ready tape =>
      simp [PrivateInitialization.step, PMF.mem_support_pure_iff] at h
      subst next
      omega

theorem initialization_peak (code : Program) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : PrivateInitialization.Control)
    (h : intermediate ∈ (eval (PrivateInitialization.step code) elapsed start).support) :
    initializationCells intermediate ≤ initializationCells start + horizon := by
  simpa using ResourceGrowth.prefix_bound (PrivateInitialization.step code) initializationCells 1
    (initialization_local code) horizon elapsed hElapsed start intermediate h

/-- At an actual return boundary, use elapsed transitions rather than the
declared time budget. These laws compose with boundary execution contracts. -/
theorem check_boundary (boundary : PreparationCheck.Control → Bool) (fuel : Nat)
    (start : PreparationCheck.Control) (result : PreparationCheck.Control × Nat)
    (h : result ∈ (runToBoundary PreparationCheck.step boundary fuel start).support) :
    checkCells result.1 ≤ checkCells start + result.2 := by
  simpa using ResourceGrowth.boundary_endpoint PreparationCheck.step checkCells 1
    check_local boundary fuel start result h

theorem export_boundary (code : Program) (boundary : ResponseExport.Control → Bool) (fuel : Nat)
    (start : ResponseExport.Control) (result : ResponseExport.Control × Nat)
    (h : result ∈ (runToBoundary (ResponseExport.step code) boundary fuel start).support) :
    exportCells result.1 ≤ exportCells start + 2 * result.2 := by
  have hb := ResourceGrowth.boundary_endpoint (ResponseExport.step code) exportCells 2
    (export_local code) boundary fuel start result h
  omega

theorem initialization_boundary (code : Program) (boundary : PrivateInitialization.Control → Bool) (fuel : Nat)
    (start : PrivateInitialization.Control) (result : PrivateInitialization.Control × Nat)
    (h : result ∈ (runToBoundary (PrivateInitialization.step code) boundary fuel start).support) :
    initializationCells result.1 ≤ initializationCells start + result.2 := by
  simpa using ResourceGrowth.boundary_endpoint (PrivateInitialization.step code) initializationCells 1
    (initialization_local code) boundary fuel start result h

end Machine.ControllerStorage
