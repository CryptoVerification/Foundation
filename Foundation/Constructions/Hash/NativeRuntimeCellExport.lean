import Foundation.Constructions.Hash.NativeRuntimeLinkedHash
import Foundation.Constructions.Hash.NativeRuntimePacketExport

/-! A physical export contract invariant under redundant tape blanks.
The actual native frame remains the output; its tape is not normalized.
The established cell-aware exporter scans this very tape. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def RuntimeCellExportable {State : Type*} (n : Nat) (frame : Configuration State) : Prop :=
  frame.control = .running (runtimeExportMachine frame) ∧
  (runtimeExportMachine frame).halted = true ∧
  (runtimeExportMachine frame).outputTape.Equivalent (ResponseLoading.loaded (runtimeExportPacket frame)) ∧
  (runtimeExportPacket frame).length = n

theorem runtimeCellExportable_invariant {State : Type*} (n : Nat)
    (c d : Configuration State) (h : CellEquivalence.Frames c d) :
    RuntimeCellExportable n c ↔ RuntimeCellExportable n d := by
  rcases c with ⟨state, control, trace⟩
  rcases d with ⟨other, otherControl, otherTrace⟩
  rcases h with ⟨rfl, rfl, h⟩
  cases h with
  | running he =>
      rename_i c d
      simp only [RuntimeCellExportable, runtimeExportMachine, runtimeExportPacket, true_and]
      rw [he.2.1, he.outputBits]
      constructor
      · intro ⟨halted, tape, length⟩
        exact ⟨halted, he.2.2.2.symm.trans tape, length⟩
      · intro ⟨halted, tape, length⟩
        exact ⟨halted, he.2.2.2.trans tape, length⟩
  | _ => simp [RuntimeCellExportable, runtimeExportMachine]

theorem typedHashFinish_cell_exportable {n κ : Nat} (pc : Nat) (input : Tape)
    (out : Outcome (CompressionInput (Bits κ) (Bits n)) (Bits n) (Bits n)
      (CompressionTable (Bits κ) (Bits n))) (prior : List (List Bool × List Bool)) :
    RuntimeCellExportable n (CellEquivalence.appendTrace prior (typedHashFinish pc input out)) := by
  have h := typedHashFinish_exportable pc input out
  change RuntimeExportable n (typedHashFinish pc input out) at h
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  change (runtimeExportMachine (typedHashFinish pc input out)).outputTape.Equivalent _
  rw [h.2.2.1]
  exact Tape.Equivalent.refl _

/-- The actual cell-equivalent hash entry satisfies the physical export
layout on every final branch, even with a nonempty cache and prior trace. -/
theorem typed_runtime_equivalent_cell_exportable {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (machine : Machine.Configuration)
    (entry : machine.Equivalent (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList))))
    (finish : Configuration (IdealTable n κ))
    (support : finish ∈ (Reification.eval (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeHashSteps n κ message.length) (NativeCode.frame (encodeCompressionTable table) prior machine)).support) :
    RuntimeCellExportable n finish := by
  apply CellEquivalence.eval_postcondition (runtimeHashCode initial.toList terminal.toList)
    (idealCompression n κ) (runtimeHashSteps n κ message.length)
    (NativeCode.frame (encodeCompressionTable table) prior machine)
    (NativeCode.frame (encodeCompressionTable table) prior
      (Machine.Configuration.initial (runtimeInputBits (message.map Bits.toList))))
    ⟨rfl, rfl, .running entry⟩ (RuntimeCellExportable n) (runtimeCellExportable_invariant n) _ finish support
  intro reference href
  simp only [NativeCode.frame] at href
  rw [CellEquivalence.eval_appendTrace] at href
  change reference ∈ ((Reification.eval _ _ _ (Configuration.initial (encodeCompressionTable table) _)).map _).support at href
  rw [typed_runtime_prefixFree_run, PMF.map_comp, PMF.mem_support_map_iff] at href
  obtain ⟨out, _, rfl⟩ := href
  exact typedHashFinish_cell_exportable _ _ out prior

/-- The physical exporter reads the actual cell-equivalent output tape,
retaining the completed frame, cache and complete query history. -/
theorem runtime_cell_export_run {State : Type*} (code : Code) (oracle : BitOracle State)
    (n : Nat) (frame : Configuration State) (valid : RuntimeCellExportable n frame) :
    TimedExecution.eval (NativePacketComponent.step code oracle) (2 * n + 5)
      (.computing frame) = PMF.pure (.exporting frame (.returned (runtimeExportPacket frame))) := by
  have h := NativePacketComponent.export_cells_run code oracle frame.state
    (runtimeExportMachine frame) frame.reverseTrace (runtimeExportPacket frame) valid.2.1 valid.2.2.1
  have frame_eq : (⟨frame.state, .running (runtimeExportMachine frame), frame.reverseTrace⟩ : Configuration State) = frame := by
    exact congrArg (fun control : Interactive.Control => (⟨frame.state, control, frame.reverseTrace⟩ : Configuration State)) valid.1.symm
  rw [frame_eq, valid.2.2.2] at h
  exact h

/-- Code relocation changes only program counters, retaining the physical
export contract and the response packet. -/
theorem runtimeCellExportable_relocation {State : Type*} (n base : Nat)
    (frame : Configuration State) :
    RuntimeCellExportable n (CodeRelocation.frame base frame) ↔ RuntimeCellExportable n frame := by
  cases frame with
  | mk state control trace =>
      cases control <;> simp [RuntimeCellExportable, runtimeExportMachine, runtimeExportPacket,
        CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
        Machine.Configuration.outputBits]

/-- Every physical final frame of the single copy-and-hash code can be
exported. No canonical tape replacement occurs between the stages. -/
theorem runtime_linked_hash_cell_exportable {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (finish : Configuration (IdealTable n κ))
    (support : finish ∈ (Reification.eval (runtimeLinkedHashCode initial.toList terminal.toList)
      (idealCompression n κ) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).support) :
    RuntimeCellExportable n finish := by
  rw [← Reification.timed_eval_eq, runToBoundary_law _ (NativeCode.returnBoundary 28)
    (runtimeTransferSteps κ message.length) (runtimeLinkedHashSteps n κ message.length) _
    (by unfold runtimeLinkedHashSteps; omega), runtime_linked_first_return,
    PMF.bind_map, PMF.mem_support_bind_iff] at support
  obtain ⟨result, hresult, support⟩ := support
  dsimp only [Function.comp_def] at support
  have layout := Machine.NativeRequestTransfer.first_layout _ _ hresult
  have stopped : result.1.halted = true := layout.2.1
  have bound := Machine.NativeRequestTransfer.first_bounded _ _ hresult
  have enough : runtimeHashSteps n κ message.length ≤ runtimeLinkedHashSteps n κ message.length - result.2 := by
    simp only [typed_runtime_input_length] at bound
    unfold runtimeLinkedHashSteps runtimeTransferSteps
    omega
  have placement : NativeCode.frame (encodeCompressionTable table) prior (Machine.Program.subroutineState 0 28 result.1) =
      CodeRelocation.frame runtimeNativePrefix.length
        (NativeCode.frame (encodeCompressionTable table) prior (result.1.resumeAt 0)) := by
    simp [Machine.Program.subroutineState, stopped, runtimeNativePrefix_length, NativeCode.frame,
      CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc, Machine.Configuration.resumeAt]
  rw [placement, runtimeLinkedHashCode, CodeRelocation.eval, PMF.mem_support_map_iff] at support
  obtain ⟨reference, href, rfl⟩ := support
  apply (runtimeCellExportable_relocation n runtimeNativePrefix.length reference).2
  rw [Reification.timed_eval_eq] at href
  have halts := typed_runtime_equivalent_halts initial terminal message table prior _
    (runtime_transfer_hash_entry message result hresult)
  have stable := Reification.eval_stable (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
    (runtimeHashSteps n κ message.length)
    (runtimeLinkedHashSteps n κ message.length - result.2 - runtimeHashSteps n κ message.length)
    (NativeCode.frame (encodeCompressionTable table) prior (result.1.resumeAt 0)) halts
  rw [Nat.add_sub_of_le enough] at stable
  rw [stable] at href
  exact typed_runtime_equivalent_cell_exportable initial terminal message table prior _
    (runtime_transfer_hash_entry message result hresult) reference href

/-- A genuine first halt also satisfies the physical contract; absorbing
padding is used only in the proof of support, never executed as export. -/
theorem runtime_linked_first_cell_exportable {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (result : Configuration (IdealTable n κ) × Nat)
    (support : result ∈ (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).support) :
    RuntimeCellExportable n result.1 := by
  have complete : Reification.terminal result.1.control = true := by
    apply runToBoundary_completes _ _ _ _ _ result support
    intro finish hf
    rw [Reification.timed_eval_eq] at hf
    exact runtime_linked_hash_halts initial terminal message table prior finish hf
  apply runtime_linked_hash_cell_exportable initial terminal message table prior result.1
  rw [← Reification.timed_eval_eq, runToBoundary_law _ (fun frame => Reification.terminal frame.control)
    (runtimeLinkedHashSteps n κ message.length) (runtimeLinkedHashSteps n κ message.length) _ (Nat.le_refl _),
    PMF.mem_support_bind_iff]
  refine ⟨result, support, ?_⟩
  rw [Reification.timed_eval_eq, Reification.eval_terminal _ _ _ _ complete]
  simp

end Foundation.Hash.Native
