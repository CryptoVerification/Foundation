import Foundation.Crypto.Semantics.Machine.SubroutineContract
import Foundation.Crypto.Semantics.Machine.NativeSequence
import Foundation.Crypto.Semantics.ProcedurePhysical
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Compile two probabilistic native contracts to one finite native program.
Both tapes pass physically into the second program. First-arrival source costs
are retained; only the final caller halt adds one transition. Logical results
are full physical configurations, so hidden seeds and scratch data survive. -/
namespace Machine.NativeCompositionContract
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} {Output : Type v} {NextOutput : Type w}
    (P : Machine.Procedure Input Output) (Q : Machine.Procedure Configuration NextOutput)

def entryPc := P.code.length + 1
def finalPc := P.code.length + Q.code.length + 2
abbrev code := P.code.followedBy Q.code

theorem first_layout : code P Q = Program.withSubroutine [] P.code
    (Q.code.asSubroutine (entryPc P) (finalPc P Q) ++ [.halt]) (entryPc P) := by
  simp [code, Program.followedBy, Program.withSubroutine, entryPc, finalPc]

theorem second_layout : code P Q = Program.withSubroutine
    (P.code.asSubroutine 0 (entryPc P)) Q.code [.halt] (finalPc P Q) := by
  simp [code, Program.followedBy, Program.withSubroutine, entryPc, finalPc, List.append_assoc]

variable
    (hPClosed : ∀ start next, start.pc < P.code.length → Step P.code start next →
      next.halted = false → next.pc < P.code.length)
    (hPEntry : ∀ input, (P.execution.entry input).pc < P.code.length)
    (hPActive : ∀ input, (P.execution.entry input).halted = false)
    (hPHalt : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).halted = true)
    (hQClosed : ∀ start next, start.pc < Q.code.length → Step Q.code start next →
      next.halted = false → next.pc < Q.code.length)
    (hQEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hQNonempty : 0 < Q.code.length)
    (hQHalt : ∀ input output, output ∈ (Q.execution.semantics input).support →
      (Q.execution.exit input output).halted = true)

noncomputable def first :=
  (SubroutineContract.call P []
    (Q.code.asSubroutine (entryPc P) (finalPc P Q) ++ [.halt]) (entryPc P)
    (by intro pc hp; simp only [List.length_nil, Nat.zero_add, entryPc]; omega)
    hPClosed hPEntry hPActive hPHalt).transport
      (stepPMF (code P Q)) id (fun _ => by rw [first_layout]; exact (PMF.map_id _).symm)

noncomputable def second :=
  (SubroutineContract.call Q (P.code.asSubroutine 0 (entryPc P)) [.halt] (finalPc P Q)
    (by intro pc hp; simp only [Program.asSubroutine_length, entryPc, finalPc]; omega)
    hQClosed (fun machine => by rw [hQEntry]; exact hQNonempty)
    (fun machine => by rw [hQEntry]; rfl) hQHalt).transport
      (stepPMF (code P Q)) id (fun _ => by rw [second_layout]; exact (PMF.map_id _).symm)

noncomputable def halt : TimedExecution.Procedure (stepPMF (code P Q)) Configuration Unit :=
  TimedExecution.Procedure.ofFixed _ (fun machine => machine.resumeAt (finalPc P Q))
    (fun machine _ => {machine.resumeAt (finalPc P Q) with halted := true})
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun machine => by
      have lookup : (code P Q)[finalPc P Q]? = some .halt := by
        rw [second_layout]
        have he : finalPc P Q = (P.code.asSubroutine 0 (entryPc P)).length + Q.code.length + 1 + 0 := by
          simp [finalPc, entryPc]
          omega
        rw [he, Program.withSubroutine_getElem?_suffix]
        rfl
      simp [TimedExecution.eval, stepPMF, next, Configuration.resumeAt, lookup,
        Instruction.next, PMF.pure_map])

variable (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support →
      Q.execution.budget ((P.execution.exit input output).resumeAt (entryPc P)) ≤ cap input)

noncomputable def body :=
  (first P Q hPClosed hPEntry hPActive hPHalt).seq
    (second P Q hQClosed hQEntry hQNonempty hQHalt)
    (by
      intro input machine hm
      change machine ∈ ((P.execution.semantics input).map
        (fun output => (P.execution.exit input output).resumeAt (entryPc P))).support at hm
      rw [PMF.mem_support_map_iff] at hm
      obtain ⟨output, _, rfl⟩ := hm
      change (Q.execution.entry ((P.execution.exit input output).resumeAt (entryPc P))).rebasePc
        (P.code.asSubroutine 0 (entryPc P)).length =
          (P.execution.exit input output).resumeAt (entryPc P)
      rw [hQEntry]
      simp [Configuration.resumeAt, Configuration.rebasePc, entryPc])
    cap
    (by
      intro input machine hm
      change machine ∈ ((P.execution.semantics input).map
        (fun output => (P.execution.exit input output).resumeAt (entryPc P))).support at hm
      rw [PMF.mem_support_map_iff] at hm
      obtain ⟨output, ho, rfl⟩ := hm
      exact hCap input output ho)

noncomputable def execution :=
  ((body P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap).seq
    ((halt P Q).reindex Prod.snd)
    (by
      intro input result hr
      change ((result.2).resumeAt (finalPc P Q)) = result.2
      change result ∈ (((first P Q hPClosed hPEntry hPActive hPHalt).semantics input).bind
        (fun middle => ((second P Q hQClosed hQEntry hQNonempty hQHalt).semantics middle).map
          (fun output => (middle, output)))).support at hr
      rw [PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, _, hr⟩ := hr
      rw [PMF.mem_support_map_iff] at hr
      obtain ⟨machine, hm, rfl⟩ := hr
      change machine ∈ ((Q.execution.semantics middle).map
        (fun output => (Q.execution.exit middle output).resumeAt (finalPc P Q))).support at hm
      rw [PMF.mem_support_map_iff] at hm
      obtain ⟨output, _, rfl⟩ := hm
      simp [Configuration.resumeAt])
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)).physical

noncomputable def native : Machine.Procedure Input Configuration :=
  ⟨code P Q, execution P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap⟩

theorem budget (input : Input) :
    (native P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap).execution.budget input =
      P.execution.budget input + cap input + 1 := rfl

theorem semantics (input : Input) :
    (native P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap).execution.semantics input =
      (P.execution.semantics input).bind (fun first =>
        (Q.execution.semantics ((P.execution.exit input first).resumeAt (entryPc P))).map
          (fun second => { (Q.execution.exit ((P.execution.exit input first).resumeAt (entryPc P)) second).resumeAt
            (finalPc P Q) with halted := true })) := by
  simp only [native, execution, TimedExecution.Procedure.physical, TimedExecution.Procedure.seq,
    body, first, second, TimedExecution.Procedure.transport, SubroutineContract.call,
    TimedExecution.Procedure.liftBoundary, SubroutineContract.stopped, TimedExecution.Procedure.ofFixed,
    TimedExecution.Procedure.reindex, halt, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, PMF.pure_map, id_eq, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Configuration.resumeAt]

/-- Full physical outcomes and actual source costs remain correlated. -/
theorem costed (input : Input) :
    (native P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap).execution.costed input =
      ((first P Q hPClosed hPEntry hPActive hPHalt).costed input).bind (fun first =>
        ((second P Q hQClosed hQEntry hQNonempty hQHalt).costed first.1).map (fun second =>
          ({second.1.resumeAt (finalPc P Q) with halted := true}, first.2 + second.2 + 1))) := by
  simp only [native, execution, body, TimedExecution.Procedure.physical, TimedExecution.Procedure.seq,
    TimedExecution.Procedure.reindex, halt, TimedExecution.Procedure.ofFixed,
    PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, PMF.pure_map]
  simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, Nat.add_assoc]

include hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt hCap in
theorem halted (input : Input) (machine : Configuration)
    (h : machine ∈ ((native P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap).execution.semantics input).support) :
    machine.halted = true := by
  rw [semantics, PMF.mem_support_bind_iff] at h
  obtain ⟨first, _, h⟩ := h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨second, _, rfl⟩ := h
  rfl

include hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt hCap in
theorem run (input : Input) (horizon : Nat)
    (hTime : P.execution.budget input + cap input + 1 ≤ horizon) :
    evalConfigWithin (code P Q) (P.execution.entry input) horizon =
      (native P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap).execution.semantics input := by
  have h := (native P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap).final_run
    input (halted P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap input)
    horizon hTime
  change evalConfigWithin (code P Q) ((P.execution.entry input).rebasePc 0) horizon =
    ((native P Q hPClosed hPEntry hPActive hPHalt hQClosed hQEntry hQNonempty hQHalt cap hCap).execution.semantics input).map id at h
  rw [PMF.map_id] at h
  have he : (P.execution.entry input).rebasePc 0 = P.execution.entry input := by
    simp [Configuration.rebasePc]
  rw [he] at h
  exact h

theorem code_length : (code P Q).length = P.code.length + Q.code.length + 3 := by
  simp [code, Program.followedBy]
  omega

end Machine.NativeCompositionContract
