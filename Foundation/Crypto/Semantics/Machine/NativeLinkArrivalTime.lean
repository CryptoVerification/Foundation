import Foundation.Crypto.Semantics.Machine.NativeLinkFixedTime

/-! Derive a typed link's actual caller-stage fixed times from the source
components' first-halt laws. Logical recovery retains the same time; no
caller input is decoded or loaded by an additional runtime instruction. -/
namespace Machine.TypedNativeComposition.Link
open Foundation.Probability TimedExecution
universe u v w x
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput} (L : Link P Q)

def firstComponent : NativeComponent Input Output where
  procedure := P
  closed := L.firstClosed
  entry := L.firstEntry
  active := L.firstActive
  halted := L.firstHalted

def secondComponent : NativeComponent NextInput NextOutput where
  procedure := Q
  closed := L.secondClosed
  entry := L.secondEntry
  active := L.secondActive
  halted := L.secondHalted

theorem first_fixed_time_of_arrival (input : Input) (duration : Nat)
    (fixed : ∀ result, result ∈ (L.firstComponent.firstArrival.procedure.execution.costed input).support → result.2 = duration)
    (result : (Input × Output) × Nat) (hResult : result ∈ (L.first.costed input).support) : result.2 = duration := by
  let suffix := Q.code.asSubroutine L.entryPc L.finalPc ++ [.halt]
  have layout : ∀ pc, pc < P.code.length → ([] : Program).length + pc ≠ L.entryPc := by
    intro pc hPc
    simp only [List.length_nil, Nat.zero_add, entryPc]
    omega
  change result ∈ ((SubroutineContract.Typed.call P [] suffix L.entryPc layout
    L.firstClosed L.firstEntry L.firstActive L.firstHalted L.read L.read_return).costed input).support at hResult
  have hPhysical : ((P.execution.exit result.1.1 result.1.2).resumeAt L.entryPc, result.2) ∈
      ((SubroutineContract.call P [] suffix L.entryPc layout L.firstClosed L.firstEntry L.firstActive L.firstHalted).costed input).support := by
    rw [← SubroutineContract.Typed.costed P [] suffix L.entryPc layout
      L.firstClosed L.firstEntry L.firstActive L.firstHalted L.read L.read_return input,
      PMF.mem_support_map_iff]
    exact ⟨result, hResult, rfl⟩
  exact L.firstComponent.invocation_fixed_time [] suffix L.entryPc layout input duration fixed _ hPhysical

theorem second_fixed_time_of_arrival (middle : Input × Output) (duration : Nat)
    (fixed : ∀ result, result ∈ (L.secondComponent.firstArrival.procedure.execution.costed (L.adapt middle.1 middle.2)).support →
      result.2 = duration)
    (result : Configuration × Nat) (hResult : result ∈ (L.second.costed middle).support) : result.2 = duration := by
  let pre := P.code.asSubroutine 0 L.entryPc
  have layout : ∀ pc, pc < Q.code.length → pre.length + pc ≠ L.finalPc := by
    intro pc hPc
    simp only [pre, Program.asSubroutine_length, entryPc, finalPc]
    omega
  change result ∈ ((SubroutineContract.call Q pre [.halt] L.finalPc layout
    L.secondClosed L.secondEntry L.secondActive L.secondHalted).costed (L.adapt middle.1 middle.2)).support at hResult
  exact L.secondComponent.invocation_fixed_time pre [.halt] L.finalPc layout
    (L.adapt middle.1 middle.2) duration fixed result hResult

end Machine.TypedNativeComposition.Link
