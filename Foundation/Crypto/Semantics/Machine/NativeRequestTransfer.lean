import Foundation.Crypto.Semantics.Machine.RetainedCopyCleanup
import Foundation.Crypto.Semantics.Machine.NativePacketService
import Foundation.Crypto.Semantics.Machine.NativeRepresentationRelation
import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.Machine.NativeComponentReindex

/-! Move a loaded raw request to the other physical tape by real native
copying, destination rewind and source erasure. Tape operands are relabeled
in the fixed code at construction time. Runtime never swaps whole tapes.
Cell-equivalent entry transport retains the actual loader blank and all
represented cells; the resulting actual exit is not normalized. -/
namespace Machine.NativeRequestTransfer
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

noncomputable def native := RetainedCopyCleanup.link.component.swapTapes

def initial (request : List Bool) : Configuration := NativePacketService.loaded request

noncomputable def input (request : List Bool) : native.EquivalentInput where
  logical := (request, [])
  actual := initial request
  equivalent := by
    change (NativePacketService.loaded request).Equivalent
      ((RetainedCopyCleanup.link.native.execution.entry (request, [])).swapTapes)
    rw [RetainedCopyCleanup.link.native_entry, RetainedCopyRewind.link.native_entry]
    change (NativePacketService.loaded request).Equivalent ((RetainedCopy.copying [] request []).swapTapes)
    have h := NativePacketService.loaded_equivalent request
    cases request <;> simpa [RetainedCopy.copying, Configuration.initial, Tape.ofBits] using h

noncomputable def component := native.equivalentEntries.reindex input

/-- This is executable finite syntax, independent of the request value. -/
def fixedCode : Program :=
  ((RetainedCopy.code.followedBy rewindBitstring.swapTapes).followedBy NativeForwardErasure.code).swapTapes

theorem component_code : component.procedure.code = fixedCode := rfl

theorem code_length : fixedCode.length = 27 := by
  change RetainedCopyCleanup.link.code.swapTapes.length = 27
  rw [Program.swapTapes_length, RetainedCopyCleanup.code_length]

theorem component_entry (request : List Bool) : component.procedure.execution.entry request = initial request := rfl

/-- An upper budget for the actual native first halt, not its exact time. -/
theorem component_budget (request : List Bool) :
    component.procedure.execution.budget request = 14 * request.length + 13 := by
  change RetainedCopyCleanup.link.native.execution.budget (request, []) = _
  rw [RetainedCopyCleanup.budget]
  simp

/-- Every actual exit has the copied request on input and an erased output
tape, with the exact original represented cells retained in that exit. -/
theorem supported_layout (request : List Bool) (target : Configuration)
    (support : target ∈ (component.procedure.execution.semantics request).support) :
    target.Equivalent
      {pc := 26, inputTape := Tape.ofBits request, halted := true} := by
  have h := native.equivalentEntries_exit (input request)
    (RetainedCopyCleanup.finish (request, [])) (RetainedCopyCleanup.semantics (request, [])) target support
  apply h.trans
  change (RetainedCopyCleanup.finish (request, [])).swapTapes.Equivalent _
  refine ⟨rfl, rfl, ?_, RetainedCopyCleanup.source_blank (request, [])⟩
  simpa [Configuration.swapTapes] using RetainedCopyCleanup.output_equivalent (request, [])

theorem run (request : List Bool) (horizon : Nat) (enough : 14 * request.length + 13 ≤ horizon) :
    evalConfigWithin fixedCode (initial request) horizon = component.procedure.execution.semantics request := by
  have h := native.equivalentEntries_run (input request) horizon
    (by change RetainedCopyCleanup.link.native.execution.budget (request, []) ≤ horizon
        rw [RetainedCopyCleanup.budget]; simpa using enough)
  exact h

/-- The full physical exit and actual time use the existing first-halt law. -/
theorem first_joint (request : List Bool) :
    component.firstArrival.procedure.execution.costed request =
    runToBoundary (stepPMF fixedCode) Configuration.halted (14 * request.length + 13) (initial request) := by
  rw [component.firstArrival_costed, component_budget]
  rfl

theorem first_layout (request : List Bool) (result : Configuration × Nat)
    (support : result ∈ (component.firstArrival.procedure.execution.costed request).support) :
    result.1.Equivalent {pc := 26, inputTape := Tape.ofBits request, halted := true} := by
  have h := component.firstArrival.procedure.execution.result_support request result support
  change result.1 ∈ ((component.procedure.execution.semantics request).map id).support at h
  rw [PMF.map_id] at h
  exact supported_layout request result.1 h

theorem first_bounded (request : List Bool) (result : Configuration × Nat)
    (support : result ∈ (component.firstArrival.procedure.execution.costed request).support) :
    result.2 ≤ 14 * request.length + 13 := by
  have h := component.firstArrival.procedure.execution.bounded request result support
  rwa [component.firstArrival_budget, component_budget] at h

theorem initial_cells (request : List Bool) : (initial request).tapeCells = request.length + 2 := by
  cases request with
  | nil => rfl
  | cons bit rest =>
      simp [initial, NativePacketService.loaded, CryptoOracle.Interactive.ResponseLoading.loaded,
        CryptoOracle.Interactive.ResponseLoading.fromCells, Configuration.tapeCells, Tape.cells]
      omega

def bitBound (size : Nat) : Nat := NativeEncodedResources.bound fixedCode 0 (size + 2) (14 * size + 13)

/-- Counts the actual loader blank, both tapes and compiled code at every
intermediate native transition, including copy and erasure in progress. -/
theorem storage_peak (request : List Bool) (elapsed : Nat) (within : elapsed ≤ 14 * request.length + 13)
    (target : Configuration)
    (support : target ∈ (TimedExecution.eval (stepPMF fixedCode) elapsed (initial request)).support) :
    (NativeEncodedResources.completeEncoding.encode (fixedCode, target)).length ≤ bitBound request.length := by
  have h := NativeEncodedResources.peak fixedCode (14 * request.length + 13) elapsed within
    (initial request) target support
  rw [initial_cells] at h
  exact h

theorem space_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 14).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 13))

end Machine.NativeRequestTransfer
