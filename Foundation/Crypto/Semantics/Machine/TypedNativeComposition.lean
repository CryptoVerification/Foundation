import Foundation.Crypto.Semantics.Machine.TypedSubroutineContract
import Foundation.Crypto.Semantics.Machine.NativeSequence
import Foundation.Crypto.Semantics.ProcedurePhysical
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Finite native composition with separately typed physical preconditions.
The second component needs contracts only on its own input type. A supported
handoff equality proves that the actual first return satisfies that physical
precondition. Decoding logical labels adds no instruction or tape preparation. -/
namespace Machine.TypedNativeComposition
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}

structure Link (P : Machine.Procedure Input Output) (Q : Machine.Procedure NextInput NextOutput) where
  firstClosed : ∀ start target, start.pc < P.code.length → Step P.code start target →
    target.halted = false → target.pc < P.code.length
  firstEntry : ∀ input, (P.execution.entry input).pc < P.code.length
  firstActive : ∀ input, (P.execution.entry input).halted = false
  firstHalted : ∀ input output, output ∈ (P.execution.semantics input).support →
    (P.execution.exit input output).halted = true
  secondClosed : ∀ start target, start.pc < Q.code.length → Step Q.code start target →
    target.halted = false → target.pc < Q.code.length
  secondEntry : ∀ input, (Q.execution.entry input).pc < Q.code.length
  secondActive : ∀ input, (Q.execution.entry input).halted = false
  secondHalted : ∀ input output, output ∈ (Q.execution.semantics input).support →
    (Q.execution.exit input output).halted = true
  read : Input → Configuration → Output
  read_return : ∀ input output, output ∈ (P.execution.semantics input).support →
    read input ((P.execution.exit input output).resumeAt (P.code.length + 1)) = output
  adapt : Input → Output → NextInput
  handoff : ∀ input output, output ∈ (P.execution.semantics input).support →
    (Q.execution.entry (adapt input output)).rebasePc (P.code.length + 1) =
      (P.execution.exit input output).resumeAt (P.code.length + 1)
  cap : Input → Nat
  bounded : ∀ input output, output ∈ (P.execution.semantics input).support →
    Q.execution.budget (adapt input output) ≤ cap input

namespace Link
variable {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput} (L : Link P Q)

def code (_ : Link P Q) : Program := P.code.followedBy Q.code
def entryPc (_ : Link P Q) : Nat := P.code.length + 1
def finalPc (_ : Link P Q) : Nat := P.code.length + Q.code.length + 2

theorem first_layout : L.code = Program.withSubroutine [] P.code
    (Q.code.asSubroutine L.entryPc L.finalPc ++ [.halt]) L.entryPc := by
  simp [code, Program.followedBy, Program.withSubroutine, entryPc, finalPc]

theorem second_layout : L.code = Program.withSubroutine
    (P.code.asSubroutine 0 L.entryPc) Q.code [.halt] L.finalPc := by
  simp [code, Program.followedBy, Program.withSubroutine, entryPc, finalPc, List.append_assoc]

noncomputable def first :=
  (SubroutineContract.Typed.call P [] (Q.code.asSubroutine L.entryPc L.finalPc ++ [.halt]) L.entryPc
    (by intro pc hp; simp only [List.length_nil, Nat.zero_add, entryPc]; omega)
    L.firstClosed L.firstEntry L.firstActive L.firstHalted L.read L.read_return).transport
      (stepPMF L.code) id (fun _ => by rw [L.first_layout]; exact (PMF.map_id _).symm)

theorem first_semantics (input : Input) : L.first.semantics input =
    (P.execution.semantics input).map (fun output => (input, output)) := by
  dsimp only [first, TimedExecution.Procedure.transport]
  apply SubroutineContract.Typed.semantics

noncomputable def second :=
  ((SubroutineContract.call Q (P.code.asSubroutine 0 L.entryPc) [.halt] L.finalPc
    (by intro pc hp; simp only [Program.asSubroutine_length, entryPc, finalPc]; omega)
    L.secondClosed L.secondEntry L.secondActive L.secondHalted).reindex
      (fun result : Input × Output => L.adapt result.1 result.2)).transport
        (stepPMF L.code) id (fun _ => by rw [L.second_layout]; exact (PMF.map_id _).symm)

noncomputable def halt : TimedExecution.Procedure (stepPMF L.code) Configuration Unit :=
  TimedExecution.Procedure.ofFixed _ (fun machine => machine.resumeAt L.finalPc)
    (fun machine _ => {machine.resumeAt L.finalPc with halted := true})
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun machine => by
      have lookup : L.code[L.finalPc]? = some .halt := by
        rw [L.second_layout]
        have he : L.finalPc = (P.code.asSubroutine 0 L.entryPc).length + Q.code.length + 1 + 0 := by
          simp [finalPc, entryPc]
          omega
        rw [he, Program.withSubroutine_getElem?_suffix]
        rfl
      simp [TimedExecution.eval, stepPMF, Machine.next, Configuration.resumeAt, lookup,
        Instruction.next, PMF.pure_map])

noncomputable def body := L.first.seq L.second
  (by
    intro input result hr
    rw [L.first_semantics, PMF.mem_support_map_iff] at hr
    obtain ⟨output, ho, rfl⟩ := hr
    change (Q.execution.entry (L.adapt input output)).rebasePc
      (P.code.asSubroutine 0 L.entryPc).length = (P.execution.exit input output).resumeAt L.entryPc
    simpa only [Program.asSubroutine_length, entryPc] using L.handoff input output ho)
  L.cap
  (by
    intro input result hr
    rw [L.first_semantics, PMF.mem_support_map_iff] at hr
    obtain ⟨output, ho, rfl⟩ := hr
    exact L.bounded input output ho)

noncomputable def execution :=
  (L.body.seq (L.halt.reindex Prod.snd)
    (by
      intro input result hr
      change result.2.resumeAt L.finalPc = result.2
      change result ∈ ((L.first.semantics input).bind
        (fun middle => (L.second.semantics middle).map (fun output => (middle, output)))).support at hr
      rw [PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, _, hr⟩ := hr
      rw [PMF.mem_support_map_iff] at hr
      obtain ⟨machine, hm, rfl⟩ := hr
      change machine ∈ ((Q.execution.semantics (L.adapt middle.1 middle.2)).map
        (fun output => (Q.execution.exit (L.adapt middle.1 middle.2) output).resumeAt L.finalPc)).support at hm
      rw [PMF.mem_support_map_iff] at hm
      obtain ⟨output, _, rfl⟩ := hm
      simp [Configuration.resumeAt])
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)).physical

noncomputable def native : Machine.Procedure Input Configuration := ⟨L.code, L.execution⟩

theorem budget (input : Input) : L.native.execution.budget input = P.execution.budget input + L.cap input + 1 := rfl

theorem semantics (input : Input) : L.native.execution.semantics input =
    (P.execution.semantics input).bind (fun output =>
      (Q.execution.semantics (L.adapt input output)).map (fun result =>
        {(Q.execution.exit (L.adapt input output) result).resumeAt L.finalPc with halted := true})) := by
  change ((L.body.seq (L.halt.reindex Prod.snd) _ _ _).physical.semantics input) = _
  simp only [TimedExecution.Procedure.physical, TimedExecution.Procedure.seq, body, first_semantics,
    second, TimedExecution.Procedure.transport, TimedExecution.Procedure.reindex,
    SubroutineContract.call, TimedExecution.Procedure.liftBoundary, SubroutineContract.stopped,
    TimedExecution.Procedure.ofFixed, halt, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, PMF.pure_map, id_eq, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Configuration.resumeAt]

/-- Physical outputs and actual first-arrival costs stay correlated. -/
theorem costed (input : Input) : L.native.execution.costed input =
    (L.first.costed input).bind (fun first => (L.second.costed first.1).map (fun second =>
      ({second.1.resumeAt L.finalPc with halted := true}, first.2 + second.2 + 1))) := by
  simp only [native, execution, body, TimedExecution.Procedure.physical, TimedExecution.Procedure.seq,
    TimedExecution.Procedure.reindex, halt, TimedExecution.Procedure.ofFixed,
    PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, PMF.pure_map]
  simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, Nat.add_assoc]

theorem halted (input : Input) (machine : Configuration)
    (h : machine ∈ (L.native.execution.semantics input).support) : machine.halted = true := by
  rw [L.semantics, PMF.mem_support_bind_iff] at h
  obtain ⟨output, _, h⟩ := h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨result, _, rfl⟩ := h
  rfl

theorem run (input : Input) (horizon : Nat) (hTime : P.execution.budget input + L.cap input + 1 ≤ horizon) :
    evalConfigWithin L.code (P.execution.entry input) horizon = L.native.execution.semantics input := by
  have h := L.native.final_run input (L.halted input) horizon hTime
  change evalConfigWithin L.code ((P.execution.entry input).rebasePc 0) horizon =
    (L.native.execution.semantics input).map id at h
  rw [PMF.map_id] at h
  simpa only [Configuration.rebasePc, Nat.zero_add] using h

theorem code_length : L.code.length = P.code.length + Q.code.length + 3 := by
  simp [code, Program.followedBy]
  omega

end Link
end Machine.TypedNativeComposition
