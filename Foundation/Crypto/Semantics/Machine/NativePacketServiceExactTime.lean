import Foundation.Crypto.Semantics.Machine.NativePacketPreparationExactTime
import Foundation.Crypto.Semantics.Machine.NativeCellResponseExactTime

/-! First packet return from a raw request, including physical loading.
Cell-equivalent entry transport preserves actual output and time while
retaining the loader's real finite tape and represented blank padding. -/
namespace Machine.NativePacketService
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

def returned : Control → Bool
  | .executing component => CellResponseExport.returned component
  | _ => false

theorem returned_absorbing (code : Program) (control : Control)
    (h : returned control = true) : step code control = PMF.pure control := by
  cases control <;> simp only [returned, Bool.false_eq_true] at h
  case executing component =>
    rw [step, CellResponseExport.returned_absorbing code component h, PMF.pure_map]

variable {Argument : Type u} {Result : Type v} (P : NativeComponent Argument Result)
    (request : List Bool) (argument : Argument)
    (hEntry : (loaded request).Equivalent (P.procedure.execution.entry argument))
    (cap : Nat)
    (hValid : ∀ result ∈ (P.procedure.execution.semantics argument).support,
      NativeCellResponse.Valid cap (P.procedure.execution.exit argument result))

include hEntry hValid in
private theorem loaded_first_joint :
    runToBoundary (step P.procedure.code) returned
      (P.procedure.execution.budget argument + (3 * cap + 4))
      (.executing (.running (loaded request))) =
    (P.firstArrival.procedure.execution.costed argument).map
      (fun result => (.executing (.returned result.1.outputBits),
        result.2 + (3 * result.1.outputBits.length + 4))) := by
  let input : NativeComponent.EquivalentInput P := ⟨argument, loaded request, hEntry⟩
  rw [runToBoundary_map (CellResponseExport.step P.procedure.code) (step P.procedure.code)
    CellResponseExport.returned returned Control.executing (fun _ => rfl) (fun _ _ => rfl)]
  have hj := NativeCellResponse.costed_is_first_return P.equivalentEntries input cap
    (NativeCellResponse.equivalent_supported P input cap hValid)
  change ((NativeCellResponse.fromEquivalent P input cap hValid).costed ()).map
    (fun result => (ResponseExport.Control.returned result.1.2, result.2)) =
      runToBoundary (CellResponseExport.step P.procedure.code) CellResponseExport.returned
        (P.procedure.execution.budget argument + (3 * cap + 4)) (.running (loaded request)) at hj
  rw [← hj, PMF.map_comp]
  have h := congrArg (fun distribution => distribution.map
    (fun result : List Bool × Nat => (Control.executing (.returned result.1), result.2)))
    (NativeCellResponse.fromEquivalent_costed P input cap hValid)
  simpa only [PMF.map_comp, Function.comp_def] using h

include hEntry hValid in
/-- The first return includes loading, native first halt and physical export. -/
theorem first_return_joint :
    runToBoundary (step P.procedure.code) returned
      ((3 * request.length + 3) + (P.procedure.execution.budget argument + (3 * cap + 4)))
      (.loading request {}) =
    (P.firstArrival.procedure.execution.costed argument).map (fun result =>
      (.executing (.returned result.1.outputBits), (3 * request.length + 3) +
        (result.2 + (3 * result.1.outputBits.length + 4)))) := by
  have hp := preparation_first_joint P.procedure.code request
  have hn := loaded_first_joint P request argument hEntry cap hValid
  rw [runToBoundary_compose (step P.procedure.code) preparedBoundary returned (fun _ => True)
    (by intros; trivial)
    (by intro control _ hb; cases control <;> simp_all [preparedBoundary, returned])
    (3 * request.length + 3) (P.procedure.execution.budget argument + (3 * cap + 4))
    (.loading request {}) trivial
    (by
      intro middle hm
      rw [hp] at hm
      have he : middle = (.executing (.running (loaded request)), 3 * request.length + 3) := by
        simpa using hm
      rw [he]; rfl)
    (by
      intro middle hm final hf
      rw [hp] at hm
      have he : middle = (.executing (.running (loaded request)), 3 * request.length + 3) := by
        simpa using hm
      rw [he] at hf
      rw [hn, PMF.mem_support_map_iff] at hf
      obtain ⟨native, _, hNative⟩ := hf
      rw [← hNative]; rfl), hp, PMF.pure_bind, hn, PMF.map_comp]
  rfl

/-- A continuing caller may use the certificate cost without counting padding. -/
theorem costed_is_first_return :
    ((service P request argument hEntry cap hValid).costed ()).map
      (fun result => (Control.executing (.returned result.1), result.2)) =
    runToBoundary (step P.procedure.code) returned
      ((3 * request.length + 3) + (P.procedure.execution.budget argument + (3 * cap + 4)))
      (.loading request {}) := by
  rw [service_costed, first_return_joint P request argument hEntry cap hValid, PMF.map_comp]
  rfl

include hEntry hValid in
/-- Increasing analysis fuel leaves the joint first-return law unchanged. -/
theorem first_return_joint_of_le (fuel : Nat)
    (hFuel : (3 * request.length + 3) +
      (P.procedure.execution.budget argument + (3 * cap + 4)) ≤ fuel) :
    runToBoundary (step P.procedure.code) returned fuel (.loading request {}) =
    (P.firstArrival.procedure.execution.costed argument).map (fun result =>
      (.executing (.returned result.1.outputBits), (3 * request.length + 3) +
        (result.2 + (3 * result.1.outputBits.length + 4)))) := by
  have hj := first_return_joint P request argument hEntry cap hValid
  rw [runToBoundary_fuel_stable (step P.procedure.code) returned
    ((3 * request.length + 3) + (P.procedure.execution.budget argument + (3 * cap + 4)))
    fuel (.loading request {}) hFuel ?_, hj]
  intro result hr
  rw [hj, PMF.mem_support_map_iff] at hr
  obtain ⟨native, _, he⟩ := hr
  rw [← he]
  rfl

end Machine.NativePacketService
