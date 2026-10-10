import Foundation.Constructions.Hash.NativeRuntimeLoadedInput
import Foundation.Crypto.Semantics.Oracle.NativeCode
import Foundation.Crypto.Semantics.Machine.NativeRequestTransfer

/-! The raw loader's output is transferred with ordinary finite native code.
Both physical tapes, redundant blanks, the private ideal cache and the full
prior transcript are retained. This is the preparation component; linking
its actual cell-equivalent exit to the hash loop remains a separate proof. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false

def runtimeTransferCode : Code := NativeCode.code Machine.NativeRequestTransfer.fixedCode

def runtimeTransferSteps (κ count : Nat) : Nat := 14 * (count * (κ + 1) + 1) + 13

def runtimeTransferStart {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n))
    (message : List (Bits κ)) (prior : List (List Bool × List Bool)) : Configuration (IdealTable n κ) :=
  NativeCode.frame (encodeCompressionTable table) prior
    (Machine.NativeRequestTransfer.initial (runtimeInputBits (message.map Bits.toList)))

variable {n κ : Nat} (message : List (Bits κ)) (table : CompressionTable (Bits κ) (Bits n))
    (prior : List (List Bool × List Bool))

/-- Same finite native transfer, executed inside the existing interactive
machine, with its genuine full-state/time law and no oracle calls. -/
theorem runtime_transfer_first_joint :
    runToBoundary (Reification.timedStep runtimeTransferCode (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeTransferSteps κ message.length)
      (runtimeTransferStart table message prior) =
    (Machine.NativeRequestTransfer.component.firstArrival.procedure.execution.costed
      (runtimeInputBits (message.map Bits.toList))).map
        (fun result => (NativeCode.frame (encodeCompressionTable table) prior result.1, result.2)) := by
  have h := NativeCode.first_joint Machine.NativeRequestTransfer.component (idealCompression n κ)
    (encodeCompressionTable table) prior (runtimeInputBits (message.map Bits.toList))
  simpa only [Machine.NativeRequestTransfer.component_code, Machine.NativeRequestTransfer.component_entry,
    Machine.NativeRequestTransfer.component_budget, typed_runtime_input_length,
    runtimeTransferCode, runtimeTransferSteps, runtimeTransferStart] using h

/-- No table reset, new sampling or transcript clearing accompanies the
copy. The actual output tape has been erased by native instructions. -/
theorem runtime_transfer_layout (result : Configuration (IdealTable n κ) × Nat)
    (support : result ∈ (runToBoundary (Reification.timedStep runtimeTransferCode (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeTransferSteps κ message.length)
      (runtimeTransferStart table message prior)).support) :
    result.1.state = encodeCompressionTable table ∧ result.1.reverseTrace = prior ∧
    ∃ machine, result.1.control = .running machine ∧
      machine.Equivalent {pc := 26, inputTape := Tape.ofBits (runtimeInputBits (message.map Bits.toList)), halted := true} ∧
      result.2 ≤ runtimeTransferSteps κ message.length := by
  rw [runtime_transfer_first_joint, PMF.mem_support_map_iff] at support
  obtain ⟨native, hn, rfl⟩ := support
  refine ⟨rfl, rfl, native.1, rfl, Machine.NativeRequestTransfer.first_layout _ _ hn, ?_⟩
  have h := Machine.NativeRequestTransfer.first_bounded _ _ hn
  simpa only [typed_runtime_input_length, runtimeTransferSteps] using h

/-- Whole-prefix storage includes the represented loader blank, both tapes,
the actual embedded instruction encoding, the private cache and prior trace. -/
theorem runtime_transfer_encoded_peak (elapsed : Nat) (within : elapsed ≤ runtimeTransferSteps κ message.length)
    (target : Configuration (IdealTable n κ))
    (support : target ∈ (Reification.eval runtimeTransferCode (idealCompression n κ) elapsed
      (runtimeTransferStart table message prior)).support) :
    (EncodedStorage.codeEncoding.encode runtimeTransferCode).length +
      ((ConfigurationEncoding.frame (tableEncoding n κ)).encode target).length ≤
    EncodedStorage.bound runtimeTransferCode 0
      (ControllerExtent.frameExtent (tableSize n κ) (runtimeTransferStart table message prior))
      (runtimeTransferSteps κ message.length) (entryIncrement n κ) n := by
  rw [← Reification.timed_eval_eq] at support
  exact EncodedStorage.encoded_peak (tableEncoding n κ) (tableSize n κ)
    (fun state => (tableEncoding_length _ _ state).le)
    runtimeTransferCode (idealCompression n κ) (entryIncrement n κ) n
    (fun state request answer ha => by
      have h := idealCompression_growth n κ state request answer ha
      exact ⟨h.1, h.2.le⟩)
    (runtimeTransferSteps κ message.length) elapsed within (runtimeTransferStart table message prior) target support

end Foundation.Hash.Native
