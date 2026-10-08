import Foundation.Crypto.Semantics.Machine.ControllerStorage

/-! Largest retained tape/list in native and physical controller states.
Copying a value preserves this measure; cellwise execution grows it slowly.
Temporary Boolean fields are bounded separately in the cell-count theorem. -/
namespace Machine.ControllerExtent
open Foundation.Probability TimedExecution

def machine (c : Configuration) : Nat := max c.inputTape.cells c.outputTape.cells

theorem instruction_bound (i : Instruction) (c d : Configuration)
    (h : d ∈ match some (i.next c) with
      | none => []
      | some (.inl target) => [target]
      | some (.inr (left, right)) => [left, right]) : machine d ≤ machine c + 1 := by
  cases i with
  | moveLeft tape =>
      simp [Instruction.next] at h
      subst d
      have hi := Tape.cells_moveLeft_le c.inputTape
      have ho := Tape.cells_moveLeft_le c.outputTape
      cases tape <;> simp only [machine, Configuration.advance, Configuration.updateTape] <;> omega
  | moveRight tape =>
      simp [Instruction.next] at h
      subst d
      have hi := Tape.cells_moveRight_le c.inputTape
      have ho := Tape.cells_moveRight_le c.outputTape
      cases tape <;> simp only [machine, Configuration.advance, Configuration.updateTape] <;> omega
  | randomBit tape =>
      simp [Instruction.next] at h
      rcases h with h | h <;> subst d <;> cases tape <;>
        simp [machine, Configuration.advance, Configuration.updateTape, Tape.cells_write]
  | write tape bit =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [machine, Configuration.advance, Configuration.updateTape, Tape.cells_write]
  | erase tape =>
      simp [Instruction.next] at h
      subst d
      cases tape <;> simp [machine, Configuration.advance, Configuration.updateTape, Tape.cells_write]
  | halt => simp [Instruction.next] at h; subst d; simp [machine]
  | branch tape a b e => simp [Instruction.next] at h; subst d; simp [machine]
  | jump pc => simp [Instruction.next] at h; subst d; simp [machine]

theorem native_bound (code : Program) (c d : Configuration)
    (h : d ∈ (stepPMF code c).support) : machine d ≤ machine c + 1 := by
  rcases (mem_support_stepPMF_iff code c d).mp h with hStep | ⟨_, rfl⟩
  · by_cases hh : c.halted = true
    · exact False.elim (no_step_of_halted hh hStep)
    · have hf : c.halted = false := by cases hflag : c.halted <;> simp_all
      cases hi : code[c.pc]? with
      | none =>
          have hd : d = { c with halted := true } := by
            simpa [Step, successors, next, hf, hi] using hStep
          subst d
          simp [machine]
      | some i =>
          apply instruction_bound i c d
          cases hn : i.next c <;> simpa [Step, successors, next, hf, hi, hn] using hStep
  · omega

def pair : PairPreparation.Control → Nat
  | .reading a b c | .checking _ a b c | .writingFirst _ _ a b c
  | .advancingFirst _ a b c | .writingSecond _ a b c | .advancingSecond a b c
  | .advancingKey a b c | .advancingMessage a b c | .checkingEnd a b c
  | .rewinding a b c | .ready a b c | .rejected a b c => max a.cells (max b.cells c.cells)

def packet : ResponsePacket.Control → Nat
  | .start response => (response.getD []).length
  | .writing remaining tape | .advancing remaining tape => max remaining.length tape.cells
  | .returned tape => tape.cells

def failure : PreparationFailure.Control → Nat
  | .detected a b c => max a.cells (max b.cells c.cells)
  | .restoring preparation => pair preparation
  | .writing a b response => max a.cells (max b.cells (packet response))
  | .returned a b c => max a.cells (max b.cells c.cells)

def check : PreparationCheck.Control → Nat
  | .preparing preparation => pair preparation
  | .failure recovery => failure recovery

def exportExtent : ResponseExport.Control → Nat
  | .running c => machine c
  | .rewinding tape => tape.cells
  | .collecting tape reversed => max tape.cells reversed.length
  | .reversing remaining response => max remaining.length response.length
  | .returned response => response.length

def initialization : PrivateInitialization.Control → Nat
  | .generating c => machine c
  | .rewinding tape | .ready tape => tape.cells

theorem pair_bound (start next : PairPreparation.Control)
    (h : next ∈ (PairPreparation.step start).support) : pair next ≤ pair start + 1 := by
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
  all_goals simp_all only [pair, Tape.cells_write]
  all_goals omega

theorem packet_bound (start next : ResponsePacket.Control)
    (h : next ∈ (ResponsePacket.step start).support) : packet next ≤ packet start + 1 := by
  cases start with
  | start response =>
      cases response <;> simp [ResponsePacket.step, PMF.mem_support_pure_iff] at h <;> subst next <;>
        simp [packet, Tape.cells, Tape.write]
  | writing remaining tape =>
      cases remaining <;> simp [ResponsePacket.step, PMF.mem_support_pure_iff] at h <;> subst next <;>
        simp [packet, Tape.cells_write] <;> omega
  | advancing remaining tape =>
      simp [ResponsePacket.step, PMF.mem_support_pure_iff] at h
      subst next
      have hb := Tape.cells_moveRight_le tape
      simp only [packet]
      omega
  | returned tape => simp [ResponsePacket.step] at h; subst next; omega

theorem failure_bound (start next : PreparationFailure.Control)
    (h : next ∈ (PreparationFailure.step start).support) : failure next ≤ failure start + 1 := by
  cases start with
  | detected a b c => simp [PreparationFailure.step] at h; subst next; simp [failure, pair]
  | restoring preparation =>
      cases preparation <;> simp only [PreparationFailure.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h; obtain ⟨value, hv, he⟩ := h; subst next
           exact pair_bound _ value hv)
        | (rw [PMF.mem_support_pure_iff] at h; subst next; simp [failure, pair, packet]; omega)
  | writing a b response =>
      cases response <;> simp only [PreparationFailure.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h; obtain ⟨value, hv, he⟩ := h; subst next
           have hb := packet_bound _ value hv
           simp only [failure] at *
           omega)
        | (rw [PMF.mem_support_pure_iff] at h; subst next; simp [failure, packet])
  | returned a b c => simp [PreparationFailure.step] at h; subst next; omega

theorem check_bound (start next : PreparationCheck.Control)
    (h : next ∈ (PreparationCheck.step start).support) : check next ≤ check start + 1 := by
  cases start with
  | preparing preparation =>
      cases preparation <;> simp only [PreparationCheck.step] at h
      all_goals first
        | (rw [PMF.mem_support_map_iff] at h; obtain ⟨value, hv, he⟩ := h; subst next
           exact pair_bound _ value hv)
        | (rw [PMF.mem_support_pure_iff] at h; subst next; simp [check, failure, pair])
  | failure recovery =>
      rw [PreparationCheck.step, PMF.mem_support_map_iff] at h
      obtain ⟨value, hv, he⟩ := h
      subst next
      exact failure_bound recovery value hv

theorem export_bound (code : Program) (start next : ResponseExport.Control)
    (h : next ∈ (ResponseExport.step code start).support) : exportExtent next ≤ exportExtent start + 1 := by
  cases start with
  | running c =>
      by_cases hh : c.halted = true
      · simp [ResponseExport.step, hh] at h; subst next; simp [exportExtent, machine]; omega
      · simp only [ResponseExport.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨value, hv, he⟩ := h
        subst next
        exact native_bound code c value hv
  | rewinding tape =>
      cases hl : tape.left <;> simp [ResponseExport.step, hl] at h <;> subst next
      · simp [exportExtent]
      · exact Tape.cells_moveLeft_le tape
  | collecting tape reversed =>
      cases hc : tape.current <;> simp [ResponseExport.step, hc] at h <;> subst next
      · simp [exportExtent]; omega
      · have hb := Tape.cells_moveRight_le tape
        simp only [exportExtent, List.length_cons]
        omega
  | reversing remaining response =>
      cases remaining <;> simp [ResponseExport.step] at h <;> subst next <;> simp [exportExtent] <;> omega
  | returned response => simp [ResponseExport.step] at h; subst next; omega

theorem initialization_bound (code : Program) (start next : PrivateInitialization.Control)
    (h : next ∈ (PrivateInitialization.step code start).support) : initialization next ≤ initialization start + 1 := by
  cases start with
  | generating c =>
      by_cases hh : c.halted = true
      · simp [PrivateInitialization.step, hh] at h; subst next; simp [initialization, machine]; omega
      · simp only [PrivateInitialization.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨value, hv, he⟩ := h
        subst next
        exact native_bound code c value hv
  | rewinding tape =>
      cases hl : tape.left <;> simp [PrivateInitialization.step, hl] at h <;> subst next
      · simp [initialization]
      · exact Tape.cells_moveLeft_le tape
  | ready tape => simp [PrivateInitialization.step] at h; subst next; omega

theorem machine_cells (c : Configuration) : c.tapeCells ≤ 2 * machine c := by
  simp only [Configuration.tapeCells, machine]
  omega

theorem pair_cells (c : PairPreparation.Control) : ControllerStorage.pairCells c ≤ 3 * pair c + 2 := by
  cases c <;> simp only [ControllerStorage.pairCells, pair] <;> omega

theorem packet_cells (c : ResponsePacket.Control) : ControllerStorage.packetCells c ≤ 2 * packet c := by
  cases c <;> simp only [ControllerStorage.packetCells, packet] <;> omega

theorem failure_cells (c : PreparationFailure.Control) : ControllerStorage.failureCells c ≤ 4 * failure c + 2 := by
  cases c with
  | detected a b c => simp only [ControllerStorage.failureCells, failure]; omega
  | restoring p =>
      have hb := pair_cells p
      simp only [ControllerStorage.failureCells, failure]
      omega
  | writing a b p =>
      have hb := packet_cells p
      simp only [ControllerStorage.failureCells, failure]
      omega
  | returned a b c => simp only [ControllerStorage.failureCells, failure]; omega

theorem check_cells (c : PreparationCheck.Control) : ControllerStorage.checkCells c ≤ 4 * check c + 2 := by
  cases c with
  | preparing p => have hb := pair_cells p; simp only [ControllerStorage.checkCells, check]; omega
  | failure p => exact failure_cells p

theorem export_cells (c : ResponseExport.Control) : ControllerStorage.exportCells c ≤ 2 * exportExtent c := by
  cases c <;> simp only [ControllerStorage.exportCells, exportExtent, Configuration.tapeCells, machine] <;> omega

theorem initialization_cells (c : PrivateInitialization.Control) :
    ControllerStorage.initializationCells c ≤ 2 * initialization c := by
  cases c <;> simp only [ControllerStorage.initializationCells, initialization, Configuration.tapeCells, machine] <;> omega

end Machine.ControllerExtent
