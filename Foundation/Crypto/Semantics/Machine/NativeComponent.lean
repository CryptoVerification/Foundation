import Foundation.Crypto.Semantics.Machine.NativeCompositionResources
import Foundation.Crypto.Semantics.Machine.NativeSequenceControl
import Foundation.Crypto.Semantics.Machine.RankedFamily

/-! Package reusable native control certificates once per component. A
compiled link is itself a component, so arbitrary finite nesting uses the
same linker rather than repeating closure, entry and halt proofs. -/
namespace Machine
open Foundation.Probability TimedExecution
universe u v w x

structure NativeComponent (Input : Type u) (Output : Type v) where
  procedure : Machine.Procedure Input Output
  closed : ∀ start target, start.pc < procedure.code.length → Step procedure.code start target →
    target.halted = false → target.pc < procedure.code.length
  entry : ∀ input, (procedure.execution.entry input).pc < procedure.code.length
  active : ∀ input, (procedure.execution.entry input).halted = false
  halted : ∀ input output, output ∈ (procedure.execution.semantics input).support →
    (procedure.execution.exit input output).halted = true

namespace NativeComponent

noncomputable def ofRankedFamily {code : Program} {Input : Type u} (F : Program.RankedFamily code Input)
    (closed : ∀ start target, start.pc < code.length → Step code start target →
      target.halted = false → target.pc < code.length)
    (entry : ∀ input, (F.entry input).pc < code.length)
    (active : ∀ input, (F.entry input).halted = false) : NativeComponent Input Configuration where
  procedure := F.native
  closed := closed
  entry := entry
  active := active
  halted := F.halted

variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}

/-- Component-specific proofs are the decoder, actual physical handoff and
second time cap. The stored control certificates are reused unchanged. -/
def link (P : NativeComponent Input Output) (Q : NativeComponent NextInput NextOutput)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      read input ((P.procedure.execution.exit input output).resumeAt (P.procedure.code.length + 1)) = output)
    (adapt : Input → Output → NextInput)
    (handoff : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      (Q.procedure.execution.entry (adapt input output)).rebasePc (P.procedure.code.length + 1) =
        (P.procedure.execution.exit input output).resumeAt (P.procedure.code.length + 1))
    (cap : Input → Nat)
    (bounded : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      Q.procedure.execution.budget (adapt input output) ≤ cap input) :
    TypedNativeComposition.Link P.procedure Q.procedure where
  firstClosed := P.closed
  firstEntry := P.entry
  firstActive := P.active
  firstHalted := P.halted
  secondClosed := Q.closed
  secondEntry := Q.entry
  secondActive := Q.active
  secondHalted := Q.halted
  read := read
  read_return := hRead
  adapt := adapt
  handoff := handoff
  cap := cap
  bounded := bounded

end NativeComponent

namespace TypedNativeComposition.Link
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput}
    (L : Link P Q)

/-- The linked finite source is globally closed, regardless of malformed
tape contents. This does not assert termination on such contents. -/
noncomputable def component : NativeComponent Input Configuration where
  procedure := L.native
  closed := Program.followedBy_control_closed P.code Q.code
  entry := fun input => by
    rw [L.native_entry]
    have h := L.firstEntry input
    change (P.execution.entry input).pc < L.code.length
    rw [L.code_length]
    omega
  active := fun input => by rw [L.native_entry]; exact L.firstActive input
  halted := L.halted

/-- Logical recovery restores the known old final address and halt flag;
the actual inherited tapes are not read into a new runtime buffer. -/
def recover (machine : Configuration) : Configuration :=
  {machine.resumeAt L.finalPc with halted := true}

theorem recover_return (input : Input) (output : Configuration)
    (hOutput : output ∈ (L.native.execution.semantics input).support) :
    L.recover (output.resumeAt (L.code.length + 1)) = output := by
  rw [L.semantics, PMF.mem_support_bind_iff] at hOutput
  obtain ⟨middle, _, hOutput⟩ := hOutput
  rw [PMF.mem_support_map_iff] at hOutput
  obtain ⟨result, _, rfl⟩ := hOutput
  simp [recover, Configuration.resumeAt]

variable {LastInput LastOutput : Type*}

noncomputable def append (R : NativeComponent LastInput LastOutput)
    (adapt : Input → Configuration → LastInput)
    (handoff : ∀ input output, output ∈ (L.native.execution.semantics input).support →
      (R.procedure.execution.entry (adapt input output)).rebasePc (L.code.length + 1) =
        output.resumeAt (L.code.length + 1))
    (cap : Input → Nat)
    (bounded : ∀ input output, output ∈ (L.native.execution.semantics input).support →
      R.procedure.execution.budget (adapt input output) ≤ cap input) :
    Link L.native R.procedure :=
  L.component.link R (fun _ => L.recover) L.recover_return adapt handoff cap bounded

theorem append_code (R : NativeComponent LastInput LastOutput) (adapt) (handoff) (cap) (bounded) :
    (L.append R adapt handoff cap bounded).code = (P.code.followedBy Q.code).followedBy R.procedure.code := rfl

theorem append_budget (R : NativeComponent LastInput LastOutput) (adapt) (handoff) (cap) (bounded)
    (input : Input) :
    (L.append R adapt handoff cap bounded).native.execution.budget input =
      P.execution.budget input + L.cap input + cap input + 2 := by
  rw [Link.budget, L.budget]
  change P.execution.budget input + L.cap input + 1 + cap input + 1 = _
  omega

theorem append_code_length (R : NativeComponent LastInput LastOutput) (adapt) (handoff) (cap) (bounded) :
    (L.append R adapt handoff cap bounded).code.length =
      P.code.length + Q.code.length + R.procedure.code.length + 6 := by
  rw [Link.code_length]
  change L.code.length + R.procedure.code.length + 3 = _
  rw [L.code_length]
  omega

/-- The three logical stages form one native program. The intermediate
physical result is the real completed first link, with both tapes intact. -/
theorem append_semantics (R : NativeComponent LastInput LastOutput)
    (adapt) (handoff) (cap) (bounded) (input : Input) :
    (L.append R adapt handoff cap bounded).native.execution.semantics input =
      (P.execution.semantics input).bind (fun first =>
        (Q.execution.semantics (L.adapt input first)).bind (fun second =>
          let middle := {(Q.execution.exit (L.adapt input first) second).resumeAt L.finalPc with halted := true}
          (R.procedure.execution.semantics (adapt input middle)).map (fun third =>
            {(R.procedure.execution.exit (adapt input middle) third).resumeAt
              (L.append R adapt handoff cap bounded).finalPc with halted := true}))) := by
  rw [Link.semantics, L.semantics]
  simp only [PMF.bind_bind, PMF.bind_map]
  rfl

end TypedNativeComposition.Link
end Machine
