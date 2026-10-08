import Foundation.Crypto.Semantics.Oracle.ControllerExtentExecution
import Foundation.Examples.CountedRejectionExperiment

/-! Polynomial peak storage for the real generated-key counted experiment.
This instance uses unit external state, empty initial transcript and marker
history, and an empty-response external oracle. All private controller data
and temporary copies are included; native code and address encodings are not. -/
namespace Foundation.CountedRejectionStorageExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u

noncomputable def emptyOracle : BitOracle Unit := fun _ _ => PMF.pure ((), [])

def caller {width : Nat} (markers : List Bool) (message : Bits width) : Configuration Unit :=
  CountedRejectionExperimentExamples.caller () [] [] markers message

def initial (width : Nat) : OneUseInitialization.Control Unit :=
  .initializing (.generating (Machine.Configuration.initial (List.replicate width true)))

def horizon (width : Nat) (markers : List Bool) : Nat :=
  markers.length * (12 * min width 1 + 36) + 50 * width + 47

def memoryBound (width : Nat) (markers : List Bool) : Nat :=
  let extent := markers.length + width + 4 + 2 * horizon width markers
  4 * extent ^ 2 + 11 * extent + 2

theorem memoryBound_eq (width : Nat) (markers : List Bool) (hWidth : 1 ≤ width) :
    memoryBound width markers =
      4 * (97 * markers.length + 101 * width + 98) ^ 2 +
      11 * (97 * markers.length + 101 * width + 98) + 2 := by
  simp only [memoryBound, horizon, Nat.min_eq_right hWidth]
  ring

theorem caller_extent {width : Nat} (markers : List Bool) (message : Bits width) :
    ControllerExtent.frameExtent (fun _ : Unit => 0) (caller markers message) ≤ markers.length + width + 4 := by
  cases markers <;> simp [caller, CountedRejectionExperimentExamples.caller,
    CountedRejectionThenEncryptExamples.start, CountedRejectionIteration.frame,
    ControllerExtent.frameExtent, ControllerExtent.controlExtent, ControllerExtent.traceExtent,
    CountedCaller.waiting, Machine.ControllerExtent.machine, RequestExport.packetTape,
    ResponseLoading.loaded, ResponseLoading.fromCells, Machine.Tape.cells] <;> omega

theorem initial_extent {width : Nat} (markers : List Bool) (message : Bits width) :
    ControllerExtent.initializationExtent (fun _ : Unit => 0) (caller markers message) (initial width) ≤
      markers.length + width + 4 := by
  have hc := caller_extent markers message
  have hg := Machine.Tape.cells_ofBits_le (List.replicate width true)
  simp only [List.length_replicate, Machine.Tape.cells] at hg
  simp only [initial, ControllerExtent.initializationExtent, Machine.ControllerExtent.initialization,
    Machine.ControllerExtent.machine, Machine.Configuration.initial]
  simp only [Machine.Tape.cells, List.length_nil]
  omega

/-- Every possible intermediate configuration, including generation,
rejection, native encryption, response delivery, and actual halt. -/
theorem peak {width : Nat} (markers : List Bool) (message : Bits width)
    (elapsed : Nat) (hElapsed : elapsed ≤ horizon width markers)
    (intermediate : OneUseInitialization.Control Unit)
    (h : intermediate ∈ (TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code
        CountedCaller.code emptyOracle (caller markers message)) elapsed (initial width)).support) :
    ControllerStorage.initializationCells (fun _ : Unit => 0) (caller markers message) intermediate ≤
      memoryBound width markers := by
  have hp := ControllerExtent.initialization_peak (fun _ : Unit => 0)
    Machine.OneTimePad.keygen Machine.OneTimePad.Prepared.listProcedure.code CountedCaller.code
    emptyOracle (caller markers message) 0 0
    (fun _ _ result hr => by
      simp only [emptyOracle, PMF.mem_support_pure_iff] at hr
      subst result
      simp)
    (horizon width markers) elapsed hElapsed (initial width) intermediate h
  have hi := initial_extent markers message
  have he : ControllerExtent.initializationExtent (fun _ : Unit => 0) (caller markers message) (initial width) +
      horizon width markers * (0 + 0 + 2) ≤ markers.length + width + 4 + 2 * horizon width markers := by omega
  have hq := Nat.pow_le_pow_left he 2
  unfold memoryBound
  nlinarith

end Foundation.CountedRejectionStorageExamples
