import Foundation.Crypto.Semantics.Machine.SubroutineContract
import Foundation.Crypto.Semantics.ProcedureIteration

/-! Typed logical results for actual probabilistic native subroutine returns.
The decoder must recover supported logical results from the actual returned
configuration. Certification adds no instructions or physical tape changes. -/
namespace Machine.SubroutineContract.Typed
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} {Output : Type v}
    (P : Machine.Procedure Input Output) (pre suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc < P.code.length → pre.length + pc ≠ returnPc)
    (hClosed : ∀ start target, start.pc < P.code.length → Step P.code start target →
      target.halted = false → target.pc < P.code.length)
    (hEntry : ∀ input, (P.execution.entry input).pc < P.code.length)
    (hActive : ∀ input, (P.execution.entry input).halted = false)
    (hHalt : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, output ∈ (P.execution.semantics input).support →
      read input ((P.execution.exit input output).resumeAt returnPc) = output)

noncomputable def call :=
  ((SubroutineContract.call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).remember).observe
    (fun result => (result.1, read result.1 result.2))
    (fun _ result => (P.execution.exit result.1 result.2).resumeAt returnPc)
    (by
      intro input result hr
      change result ∈ (((SubroutineContract.call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).semantics input).map
        (fun machine => (input, machine))).support at hr
      rw [PMF.mem_support_map_iff] at hr
      obtain ⟨machine, hm, rfl⟩ := hr
      rw [SubroutineContract.call_semantics, PMF.mem_support_map_iff] at hm
      obtain ⟨output, ho, rfl⟩ := hm
      simp only [hRead input output ho]
      rfl)

theorem budget (input : Input) :
    (call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt read hRead).budget input =
      P.execution.budget input := rfl

theorem exit (input : Input) (result : Input × Output) :
    (call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt read hRead).exit input result =
      (P.execution.exit result.1 result.2).resumeAt returnPc := rfl

theorem semantics (input : Input) :
    (call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt read hRead).semantics input =
      (P.execution.semantics input).map (fun output => (input, output)) := by
  change (((P.execution.semantics input).map _).map _).map _ = _
  rw [PMF.map_comp, PMF.map_comp]
  rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext output ho
  simp only [Function.comp_def, hRead input output ho]

/-- The original first-arrival times and physical endpoints are preserved;
the new logical labels only decode already returned configurations. -/
theorem costed (input : Input) :
    ((call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt read hRead).costed input).map
      (fun result => ((P.execution.exit result.1.1 result.1.2).resumeAt returnPc, result.2)) =
      (SubroutineContract.call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).costed input := by
  -- Preserve cost correlations using the actual costed support, not marginals.
  change ((((SubroutineContract.call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).costed input).map _).map _).map _ = _
  rw [PMF.map_comp, PMF.map_comp]
  conv_rhs => rw [← PMF.map_id ((SubroutineContract.call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).costed input)]
  rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hr
  have hm := (SubroutineContract.call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).result_support input result hr
  rw [SubroutineContract.call_semantics, PMF.mem_support_map_iff] at hm
  obtain ⟨output, ho, he⟩ := hm
  simp only [Function.comp_def, ← he, hRead input output ho, id_eq]
  exact congrArg PMF.pure (Prod.ext he rfl)

end Machine.SubroutineContract.Typed
