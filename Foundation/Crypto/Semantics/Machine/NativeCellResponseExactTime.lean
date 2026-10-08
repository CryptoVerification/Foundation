import Foundation.Crypto.Semantics.Machine.NativeCellResponse
import Foundation.Crypto.Semantics.Machine.CellResponseExportExactTime
import Foundation.Crypto.Semantics.BoundaryComposition

/-! Compose native first halt with physical export first return.
Unlike an operational certificate alone, this excludes an earlier packet
return and removes all unused analysis fuel from the joint time law. -/
namespace Machine.NativeCellResponse
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

variable {Argument : Type u} {Result : Type v} (P : NativeComponent Argument Result)
    (argument : Argument) (cap : Nat)
    (hValid : ∀ result ∈ (P.procedure.execution.semantics argument).support,
      Valid cap (P.procedure.execution.exit argument result))

include hValid in
theorem first_return_joint :
    runToBoundary (CellResponseExport.step P.procedure.code) CellResponseExport.returned
      (P.procedure.execution.budget argument + (3 * cap + 4))
      (.running (P.procedure.execution.entry argument)) =
    (P.firstArrival.procedure.execution.costed argument).map
      (fun result => (.returned result.1.outputBits,
        result.2 + (3 * result.1.outputBits.length + 4))) := by
  have hNative :
      runToBoundary (CellResponseExport.step P.procedure.code) boundary
        (P.procedure.execution.budget argument) (.running (P.procedure.execution.entry argument)) =
      (P.firstArrival.procedure.execution.costed argument).map
        (fun result => (ResponseExport.Control.running result.1, result.2)) := by
    rw [runToBoundary_map (stepPMF P.procedure.code) (CellResponseExport.step P.procedure.code)
      Configuration.halted boundary ResponseExport.Control.running (fun _ => rfl)
      (fun machine h => by simp [CellResponseExport.step, h]), P.firstArrival_costed]
  have hv : ∀ result ∈ (P.firstArrival.procedure.execution.costed argument).support,
      Valid cap result.1 := by
    intro result hr
    have hs := P.firstArrival.procedure.execution.result_support argument result hr
    change result.1 ∈ ((P.procedure.execution.semantics argument).map
      (P.procedure.execution.exit argument)).support at hs
    rw [PMF.mem_support_map_iff] at hs
    obtain ⟨output, ho, he⟩ := hs
    rw [← he]
    exact hValid output ho
  have hMiddle : ∀ middle ∈
      (runToBoundary (CellResponseExport.step P.procedure.code) boundary
        (P.procedure.execution.budget argument) (.running (P.procedure.execution.entry argument))).support,
      ∃ result ∈ (P.firstArrival.procedure.execution.costed argument).support,
        middle = (.running result.1, result.2) := by
    intro middle hm
    rw [hNative, PMF.mem_support_map_iff] at hm
    obtain ⟨result, hr, he⟩ := hm
    exact ⟨result, hr, he.symm⟩
  have hExport : ∀ result ∈ (P.firstArrival.procedure.execution.costed argument).support,
      runToBoundary (CellResponseExport.step P.procedure.code) CellResponseExport.returned
        (3 * cap + 4) (.running result.1) =
      PMF.pure (.returned result.1.outputBits, 3 * result.1.outputBits.length + 4) := by
    intro result hr
    have hh := hv result hr
    exact CellResponseExport.first_return_joint_of_le P.procedure.code result.1
      result.1.outputBits hh.1 hh.2.1 (3 * cap + 4) (by have := hh.2.2; omega)
  rw [runToBoundary_compose (CellResponseExport.step P.procedure.code) boundary
    CellResponseExport.returned (fun control => ∃ machine, control = .running machine)
    (by
      intro control hc hb next hn
      obtain ⟨machine, rfl⟩ := hc
      change machine.halted = false at hb
      simp only [CellResponseExport.step, hb, Bool.false_eq_true, ↓reduceIte,
        PMF.mem_support_map_iff] at hn
      obtain ⟨target, _, he⟩ := hn
      exact ⟨target, he.symm⟩)
    (by intro control hc _; obtain ⟨machine, rfl⟩ := hc; rfl)
    (P.procedure.execution.budget argument) (3 * cap + 4)
    (.running (P.procedure.execution.entry argument)) ⟨_, rfl⟩
    (by
      intro middle hm
      obtain ⟨result, hr, rfl⟩ := hMiddle middle hm
      exact (hv result hr).1)
    (by
      intro middle hm final hf
      obtain ⟨result, hr, rfl⟩ := hMiddle middle hm
      rw [hExport result hr] at hf
      have he : final = (.returned result.1.outputBits, 3 * result.1.outputBits.length + 4) := by
        simpa using hf
      rw [he]; rfl), hNative, PMF.bind_map]
  conv_rhs => rw [PMF.map]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hr
  simp only [Function.comp_def]
  rw [hExport result hr, PMF.pure_map]

include hValid in
/-- The same actual time law holds at every sufficient analysis horizon. -/
theorem first_return_joint_of_le (fuel : Nat)
    (hFuel : P.procedure.execution.budget argument + (3 * cap + 4) ≤ fuel) :
    runToBoundary (CellResponseExport.step P.procedure.code) CellResponseExport.returned fuel
      (.running (P.procedure.execution.entry argument)) =
    (P.firstArrival.procedure.execution.costed argument).map
      (fun result => (.returned result.1.outputBits,
        result.2 + (3 * result.1.outputBits.length + 4))) := by
  have hj := first_return_joint P argument cap hValid
  rw [runToBoundary_fuel_stable (CellResponseExport.step P.procedure.code)
    CellResponseExport.returned (P.procedure.execution.budget argument + (3 * cap + 4))
    fuel (.running (P.procedure.execution.entry argument)) hFuel ?_, hj]
  intro result hr
  rw [hj, PMF.mem_support_map_iff] at hr
  obtain ⟨native, _, he⟩ := hr
  rw [← he]
  rfl

/-- The existing composite certificate records precisely the first return.
This extra theorem is needed before a continuing caller can reuse its time. -/
theorem costed_is_first_return :
    ((whole P argument cap hValid).costed ()).map
      (fun result => (ResponseExport.Control.returned result.1.2, result.2)) =
    runToBoundary (CellResponseExport.step P.procedure.code) CellResponseExport.returned
      (P.procedure.execution.budget argument + (3 * cap + 4))
      (.running (P.procedure.execution.entry argument)) := by
  have h := congrArg (fun distribution => distribution.map
    (fun result : List Bool × Nat => (ResponseExport.Control.returned result.1, result.2)))
    (costed P argument cap hValid)
  rw [first_return_joint P argument cap hValid]
  simpa only [PMF.map_comp, Function.comp_def] using h

end Machine.NativeCellResponse
