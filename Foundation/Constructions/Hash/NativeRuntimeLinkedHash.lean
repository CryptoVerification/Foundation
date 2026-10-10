import Foundation.Constructions.Hash.NativeRuntimeEquivalentInput
import Foundation.Crypto.Semantics.Oracle.NativeSubroutine
import Foundation.Crypto.Semantics.Oracle.CodeRelocation

/-! A single interactive finite code physically copies the loaded request,
cleans up its source, jumps into the relocated hash code, and hashes the
runtime message. No host tape swap, normalization or resumption is executed
between these stages. The ideal compression capability remains atomic. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def runtimeNativePrefix : Code := NativeCode.subroutinePrefix Machine.NativeRequestTransfer.fixedCode

def runtimeLinkedHashCode (initial terminal : List Bool) : Code :=
  CodeRelocation.host runtimeNativePrefix (runtimeHashCode initial terminal)

def runtimeLinkedHashSteps (n κ count : Nat) : Nat :=
  runtimeTransferSteps κ count + runtimeHashSteps n κ count

theorem runtimeNativePrefix_length : runtimeNativePrefix.length = 28 := by
  rw [runtimeNativePrefix, NativeCode.subroutinePrefix_length, Machine.NativeRequestTransfer.code_length]

theorem runtimeLinkedHashCode_length (initial terminal : List Bool) :
    (runtimeLinkedHashCode initial terminal).length = 7 * initial.length + 11 * terminal.length + 41 := by
  rw [runtimeLinkedHashCode, CodeRelocation.code_length, runtimeNativePrefix_length, runtimeHashCode_length]
  omega

/-- The cleanup's original halt is a real return jump, preserving the
joint distribution of physical tapes and actual transition count. -/
theorem runtime_linked_first_return {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool)) :
    runToBoundary (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (NativeCode.returnBoundary 28) (runtimeTransferSteps κ message.length)
      (runtimeTransferStart table message prior) =
    (Machine.NativeRequestTransfer.component.firstArrival.procedure.execution.costed
      (runtimeInputBits (message.map Bits.toList))).map
        (fun result => (NativeCode.frame (encodeCompressionTable table) prior
          (Machine.Program.subroutineState 0 28 result.1), result.2)) := by
  have h := NativeCode.subroutine_first_joint Machine.NativeRequestTransfer.component
    ((runtimeHashCode initial.toList terminal.toList).map (CodeRelocation.instruction runtimeNativePrefix.length))
    (idealCompression n κ) (encodeCompressionTable table) prior (runtimeInputBits (message.map Bits.toList))
  simpa only [Machine.NativeRequestTransfer.component_code, Machine.NativeRequestTransfer.component_entry,
    Machine.NativeRequestTransfer.component_budget, Machine.NativeRequestTransfer.code_length,
    typed_runtime_input_length, runtimeLinkedHashCode, CodeRelocation.host, runtimeNativePrefix,
    runtimeTransferSteps, runtimeTransferStart] using h

private theorem relocated_observation {State : Type*} (base : Nat) (frame : Configuration State) :
    CellEquivalence.packetObservation (CodeRelocation.frame base frame) =
      CellEquivalence.packetObservation frame := by
  simp only [CellEquivalence.packetObservation, CodeRelocation.frame, CodeRelocation.packet]

/-- After the real return, the remaining budget executes the relocated
hash on exactly the inherited tapes, retaining the original cache/history. -/
theorem runtime_linked_residual_packet {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (result : Machine.Configuration × Nat)
    (support : result ∈ (Machine.NativeRequestTransfer.component.firstArrival.procedure.execution.costed
      (runtimeInputBits (message.map Bits.toList))).support) :
    (TimedExecution.eval
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (runtimeLinkedHashSteps n κ message.length - result.2)
      (NativeCode.frame (encodeCompressionTable table) prior (Machine.Program.subroutineState 0 28 result.1))).map
        CellEquivalence.packetObservation =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (fun out => (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) := by
  have layout := Machine.NativeRequestTransfer.first_layout _ _ support
  have stopped : result.1.halted = true := layout.2.1
  have bound := Machine.NativeRequestTransfer.first_bounded _ _ support
  have enough : runtimeHashSteps n κ message.length ≤ runtimeLinkedHashSteps n κ message.length - result.2 := by
    simp only [typed_runtime_input_length] at bound
    unfold runtimeLinkedHashSteps runtimeTransferSteps
    omega
  have placement : NativeCode.frame (encodeCompressionTable table) prior (Machine.Program.subroutineState 0 28 result.1) =
      CodeRelocation.frame runtimeNativePrefix.length
        (NativeCode.frame (encodeCompressionTable table) prior (result.1.resumeAt 0)) := by
    simp [Machine.Program.subroutineState, stopped, runtimeNativePrefix_length, NativeCode.frame,
      CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc, Machine.Configuration.resumeAt]
  rw [placement, runtimeLinkedHashCode, CodeRelocation.eval, PMF.map_comp]
  simp only [Function.comp_def, relocated_observation]
  rw [Reification.timed_eval_eq]
  have halts := typed_runtime_equivalent_halts initial terminal message table prior _
    (runtime_transfer_hash_entry message result support)
  have stable := Reification.eval_stable (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ)
    (runtimeHashSteps n κ message.length)
    (runtimeLinkedHashSteps n κ message.length - result.2 - runtimeHashSteps n κ message.length)
    (NativeCode.frame (encodeCompressionTable table) prior (result.1.resumeAt 0)) halts
  rw [Nat.add_sub_of_le enough] at stable
  rw [stable]
  exact runtime_transfer_hash_packet initial terminal message table prior result support

/-- Full finite-code execution from the actual raw-loader output realizes
the original typed hash, using real copying and an actual return jump. -/
theorem runtime_linked_hash_packet {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool)) :
    (Reification.eval (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeLinkedHashSteps n κ message.length) (runtimeTransferStart table message prior)).map
        CellEquivalence.packetObservation =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (fun out => (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) := by
  rw [← Reification.timed_eval_eq, runToBoundary_law _ (NativeCode.returnBoundary 28)
    (runtimeTransferSteps κ message.length) (runtimeLinkedHashSteps n κ message.length) _
    (by unfold runtimeLinkedHashSteps; omega), runtime_linked_first_return,
    PMF.map_bind, PMF.bind_map]
  rw [← PMF.bindOnSupport_eq_bind]
  calc
    _ = (Machine.NativeRequestTransfer.component.firstArrival.procedure.execution.costed
        (runtimeInputBits (message.map Bits.toList))).bindOnSupport (fun _ _ =>
          ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
            (fun out => (some out.result.toList, encodeCompressionTable out.state,
              (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior))) := by
      congr 1
      funext result support
      exact runtime_linked_residual_packet initial terminal message table prior result support
    _ = _ := by rw [PMF.bindOnSupport_eq_bind, PMF.bind_const]

/-- Every supported branch of the linked code genuinely reaches a halt. -/
theorem runtime_linked_hash_halts {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool)) :
    Reification.HaltsWithin (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ)
      (runtimeTransferStart table message prior) (runtimeLinkedHashSteps n κ message.length) := by
  intro finish support
  have seen : CellEquivalence.packetObservation finish ∈
      ((Reification.eval (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ)
        (runtimeLinkedHashSteps n κ message.length) (runtimeTransferStart table message prior)).map
          CellEquivalence.packetObservation).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, support, rfl⟩
  rw [runtime_linked_hash_packet, PMF.mem_support_map_iff] at seen
  obtain ⟨out, _, he⟩ := seen
  have hp := congrArg Prod.fst he
  change some out.result.toList = Reification.packet finish.control at hp
  have somePacket : (Reification.packet finish.control).isSome = true := by rw [← hp]; rfl
  cases hc : finish.control with
  | running machine =>
      cases hh : machine.halted <;> simp_all [Reification.packet, Reification.terminal]
  | _ => simp_all [Reification.packet, Reification.terminal]

/-- Real copying and its return jump issue no compression queries. The
linked hash adds exactly L+1 calls to the original complete history. -/
theorem runtime_linked_hash_queries {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (finish : Configuration (IdealTable n κ))
    (support : finish ∈ (Reification.eval (runtimeLinkedHashCode initial.toList terminal.toList)
      (idealCompression n κ) (runtimeLinkedHashSteps n κ message.length)
      (runtimeTransferStart table message prior)).support) :
    finish.reverseTrace.length = message.length + 1 + prior.length := by
  have seen : CellEquivalence.packetObservation finish ∈
      ((Reification.eval (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ)
        (runtimeLinkedHashSteps n κ message.length) (runtimeTransferStart table message prior)).map
          CellEquivalence.packetObservation).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, support, rfl⟩
  rw [runtime_linked_hash_packet, PMF.mem_support_map_iff] at seen
  obtain ⟨out, hout, he⟩ := seen
  have trace := congrArg (fun value : Option (List Bool) × IdealTable n κ × List (List Bool × List Bool) => value.2.2) he
  simp only [CellEquivalence.packetObservation] at trace
  rw [← trace, List.length_append, List.length_reverse, List.length_map]
  have count := iterate_trace_length RandomOracle.oracle initial (Foundation.Hash.encode terminal message) table out hout
  simpa using congrArg (fun length => length + prior.length) count

/-- All intermediate states of the one actual code are counted, including
copy, erase, return jump, hashing, private cache and the existing trace. -/
theorem runtime_linked_hash_encoded_peak {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ))
    (table : CompressionTable (Bits κ) (Bits n)) (prior : List (List Bool × List Bool))
    (elapsed : Nat) (within : elapsed ≤ runtimeLinkedHashSteps n κ message.length)
    (target : Configuration (IdealTable n κ))
    (support : target ∈ (Reification.eval (runtimeLinkedHashCode initial.toList terminal.toList)
      (idealCompression n κ) elapsed (runtimeTransferStart table message prior)).support) :
    (EncodedStorage.codeEncoding.encode (runtimeLinkedHashCode initial.toList terminal.toList)).length +
      ((ConfigurationEncoding.frame (tableEncoding n κ)).encode target).length ≤
    EncodedStorage.bound (runtimeLinkedHashCode initial.toList terminal.toList) 0
      (ControllerExtent.frameExtent (tableSize n κ) (runtimeTransferStart table message prior))
      (runtimeLinkedHashSteps n κ message.length) (entryIncrement n κ) n := by
  rw [← Reification.timed_eval_eq] at support
  exact EncodedStorage.encoded_peak (tableEncoding n κ) (tableSize n κ)
    (fun state => (tableEncoding_length _ _ state).le)
    (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) (entryIncrement n κ) n
    (fun state request answer ha => by
      have h := idealCompression_growth n κ state request answer ha
      exact ⟨h.1, h.2.le⟩)
    (runtimeLinkedHashSteps n κ message.length) elapsed within
    (runtimeTransferStart table message prior) target support

end Foundation.Hash.Native
