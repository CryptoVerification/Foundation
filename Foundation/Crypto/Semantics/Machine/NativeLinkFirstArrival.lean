import Foundation.Crypto.Semantics.Machine.NativeInvocationComposition
import Foundation.Crypto.Semantics.Machine.NativeLinkArrivalTime

/-! Actual first-halt composition for arbitrary finite native links.
Component costs may depend on their inputs and random outcomes, and their
termination bounds may include slack. No constant-time premise is used. -/
namespace Machine.TypedNativeComposition.Link
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput} (L : Link P Q)

theorem second_return (middle : Input × Output) (result : Configuration × Nat)
    (hResult : result ∈ (L.second.costed middle).support) : result.1.resumeAt L.finalPc = result.1 := by
  have hLogical := L.second.result_support middle result hResult
  change result.1 ∈ ((Q.execution.semantics (L.adapt middle.1 middle.2)).map
    (fun output => (Q.execution.exit (L.adapt middle.1 middle.2) output).resumeAt L.finalPc)).support at hLogical
  rw [PMF.mem_support_map_iff] at hLogical
  obtain ⟨output, _, hEq⟩ := hLogical
  rw [← hEq]
  simp [Configuration.resumeAt]

theorem second_firstHalt_costed (middle : Input × Output) (fuel : Nat)
    (bounded : Q.execution.budget (L.adapt middle.1 middle.2) ≤ fuel) :
    runToBoundary (stepPMF L.code) Configuration.halted (fuel + 1) (L.second.entry middle) =
      (L.second.costed middle).map
        (fun result => ({result.1.resumeAt L.finalPc with halted := true}, result.2 + 1)) := by
  let pre := P.code.asSubroutine 0 L.entryPc
  have layout : ∀ pc, pc < Q.code.length → pre.length + pc ≠ L.finalPc := by
    intro pc hPc
    simp only [pre, Program.asSubroutine_length, entryPc, finalPc]
    omega
  have hCode : Program.withSubroutine pre Q.code [.halt] L.finalPc = L.code := L.second_layout.symm
  have lookup : (Program.withSubroutine pre Q.code [.halt] L.finalPc)[L.finalPc]? = some .halt := by
    have hPc : L.finalPc = pre.length + Q.code.length + 1 + 0 := by
      simp only [pre, Program.asSubroutine_length, entryPc, finalPc]
      omega
    rw [hPc, Program.withSubroutine_getElem?_suffix]
    rfl
  have h := L.secondComponent.invocation_then_halt pre [.halt] L.finalPc layout
    (L.adapt middle.1 middle.2) lookup
  change runToBoundary (stepPMF (Program.withSubroutine pre Q.code [.halt] L.finalPc)) Configuration.halted
    (Q.execution.budget (L.adapt middle.1 middle.2) + 1)
    ((Q.execution.entry (L.adapt middle.1 middle.2)).rebasePc pre.length) =
    (L.second.costed middle).map (fun result => ({result.1 with halted := true}, result.2 + 1)) at h
  rw [hCode] at h
  change runToBoundary (stepPMF L.code) Configuration.halted
    (Q.execution.budget (L.adapt middle.1 middle.2) + 1) (L.second.entry middle) = _ at h
  rw [runToBoundary_fuel_stable _ _ (Q.execution.budget (L.adapt middle.1 middle.2) + 1)
    (fuel + 1) _ (by omega) (by
      intro result hResult
      rw [h, PMF.mem_support_map_iff] at hResult
      obtain ⟨original, _, rfl⟩ := hResult
      rfl), h]
  rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  change PMF.pure ({result.1 with halted := true}, result.2 + 1) =
    PMF.pure ({result.1.resumeAt L.finalPc with halted := true}, result.2 + 1)
  rw [L.second_return middle result hResult]

/-- Every finite native link already reports its actual first global halt.
This includes variable-time callees and conservative source bounds. -/
theorem firstArrival_costed_eq (input : Input) :
    L.component.firstArrival.procedure.execution.costed input = L.native.execution.costed input := by
  let suffix := Q.code.asSubroutine L.entryPc L.finalPc ++ [.halt]
  have layout : ∀ pc, pc < P.code.length → ([] : Program).length + pc ≠ L.entryPc := by
    intro pc hPc
    simp only [List.length_nil, Nat.zero_add, entryPc]
    omega
  have hCode : Program.withSubroutine [] P.code suffix L.entryPc = L.code := L.first_layout.symm
  have hFirst : (L.firstComponent.invocation [] suffix L.entryPc layout).costed input =
      (L.first.costed input).map (fun result => (L.first.exit input result.1, result.2)) := by
    unfold NativeComponent.invocation
    change (SubroutineContract.call P [] suffix L.entryPc layout
      L.firstClosed L.firstEntry L.firstActive L.firstHalted).costed input =
      ((SubroutineContract.Typed.call P [] suffix L.entryPc layout
        L.firstClosed L.firstEntry L.firstActive L.firstHalted L.read L.read_return).costed input).map
        (fun result => ((P.execution.exit result.1.1 result.1.2).resumeAt L.entryPc, result.2))
    exact (SubroutineContract.Typed.costed P [] suffix L.entryPc layout
      L.firstClosed L.firstEntry L.firstActive L.firstHalted L.read L.read_return input).symm
  have hHandoff (middle : (Input × Output) × Nat)
      (hMiddle : middle ∈ (L.first.costed input).support) :
      L.second.entry middle.1 = L.first.exit input middle.1 ∧
        Q.execution.budget (L.adapt middle.1.1 middle.1.2) ≤ L.cap input := by
    have hLogical := L.first.result_support input middle hMiddle
    rw [L.first_semantics, PMF.mem_support_map_iff] at hLogical
    obtain ⟨output, hOutput, hPair⟩ := hLogical
    have hInput : middle.1.1 = input := (congrArg Prod.fst hPair).symm
    have hValue : middle.1.2 = output := (congrArg Prod.snd hPair).symm
    constructor
    · change (Q.execution.entry (L.adapt middle.1.1 middle.1.2)).rebasePc
        (P.code.asSubroutine 0 L.entryPc).length = (P.execution.exit middle.1.1 middle.1.2).resumeAt L.entryPc
      rw [hInput, hValue, Program.asSubroutine_length]
      exact L.handoff input output hOutput
    · rw [hInput, hValue]
      exact L.bounded input output hOutput
  have h := L.firstComponent.invocation_firstHalt_compose [] suffix L.entryPc layout input (L.cap input + 1) (by
    intro middle hMiddle result hResult
    rw [hFirst, PMF.mem_support_map_iff] at hMiddle
    obtain ⟨original, hOriginal, rfl⟩ := hMiddle
    change result ∈ (runToBoundary (stepPMF (Program.withSubroutine [] P.code suffix L.entryPc))
      Configuration.halted (L.cap input + 1) (L.first.exit input original.1)).support at hResult
    rw [hCode, ← (hHandoff original hOriginal).1,
      L.second_firstHalt_costed original.1 (L.cap input) (hHandoff original hOriginal).2,
      PMF.mem_support_map_iff] at hResult
    obtain ⟨last, _, rfl⟩ := hResult
    rfl)
  rw [hFirst, PMF.bind_map] at h
  change runToBoundary (stepPMF (Program.withSubroutine [] P.code suffix L.entryPc)) Configuration.halted
    (P.execution.budget input + (L.cap input + 1)) ((P.execution.entry input).rebasePc 0) =
    (L.first.costed input).bind (fun middle =>
      (runToBoundary (stepPMF (Program.withSubroutine [] P.code suffix L.entryPc)) Configuration.halted
        (L.cap input + 1) (L.first.exit input middle.1)).map (fun result => (result.1, middle.2 + result.2))) at h
  rw [hCode] at h
  rw [L.component.firstArrival_costed]
  change runToBoundary (stepPMF L.code) Configuration.halted
    (P.execution.budget input + L.cap input + 1) ((P.execution.entry input).rebasePc 0) = _
  rw [Nat.add_assoc, h, L.costed]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext middle hMiddle
  rw [← (hHandoff middle hMiddle).1,
    L.second_firstHalt_costed middle.1 (L.cap input) (hHandoff middle hMiddle).2, PMF.map_comp]
  simp only [Function.comp_def, Nat.add_assoc]

theorem firstArrival_costed (input : Input) :
    L.component.firstArrival.procedure.execution.costed input =
      (L.first.costed input).bind (fun first => (L.second.costed first.1).map (fun second =>
        ({second.1.resumeAt L.finalPc with halted := true}, first.2 + second.2 + 1))) := by
  rw [L.firstArrival_costed_eq, L.costed]

theorem first_costed_of_arrival (input : Input) :
    L.first.costed input = (L.firstComponent.firstArrival.procedure.execution.costed input).map
      (fun result => ((input, L.read input (result.1.resumeAt L.entryPc)), result.2)) := by
  let suffix := Q.code.asSubroutine L.entryPc L.finalPc ++ [.halt]
  have layout : ∀ pc, pc < P.code.length → ([] : Program).length + pc ≠ L.entryPc := by
    intro pc hPc
    simp only [List.length_nil, Nat.zero_add, entryPc]
    omega
  change (((L.firstComponent.invocation [] suffix L.entryPc layout).costed input).map
    (fun result => ((input, result.1), result.2))).map
    (fun result => ((result.1.1, L.read result.1.1 result.1.2), result.2)) = _
  rw [L.firstComponent.invocation_costed, PMF.map_comp, PMF.map_comp]
  rfl

theorem second_costed_of_arrival (middle : Input × Output) :
    L.second.costed middle =
      (L.secondComponent.firstArrival.procedure.execution.costed (L.adapt middle.1 middle.2)).map
        (fun result => (result.1.resumeAt L.finalPc, result.2)) := by
  let pre := P.code.asSubroutine 0 L.entryPc
  have layout : ∀ pc, pc < Q.code.length → pre.length + pc ≠ L.finalPc := by
    intro pc hPc
    simp only [pre, Program.asSubroutine_length, entryPc, finalPc]
    omega
  exact L.secondComponent.invocation_costed pre [.halt] L.finalPc layout (L.adapt middle.1 middle.2)

/-- Derive the entire linked joint law from the source components' actual
first-halt laws, preserving adaptive inputs and state/time correlations. -/
theorem firstArrival_costed_from_components (input : Input) :
    L.component.firstArrival.procedure.execution.costed input =
      (L.firstComponent.firstArrival.procedure.execution.costed input).bind (fun first =>
        (L.secondComponent.firstArrival.procedure.execution.costed
          (L.adapt input (L.read input (first.1.resumeAt L.entryPc)))).map (fun second =>
            ({second.1.resumeAt L.finalPc with halted := true}, first.2 + second.2 + 1))) := by
  rw [L.firstArrival_costed, L.first_costed_of_arrival, PMF.bind_map]
  congr 1
  funext first
  dsimp only [Function.comp_def]
  rw [L.second_costed_of_arrival, PMF.map_comp]
  rfl

theorem firstArrival_joint_of_fixed_calls (input : Input) (firstTime secondTime : Nat)
    (fixedFirst : ∀ result, result ∈ (L.first.costed input).support → result.2 = firstTime)
    (fixedSecond : ∀ middle, middle ∈ (L.first.costed input).support →
      ∀ result, result ∈ (L.second.costed middle.1).support → result.2 = secondTime) :
    L.component.firstArrival.procedure.execution.costed input =
      (L.native.execution.semantics input).map (fun state => (state, firstTime + secondTime + 1)) := by
  rw [L.firstArrival_costed_eq, L.joint_of_fixed_time input firstTime secondTime fixedFirst fixedSecond]

end Machine.TypedNativeComposition.Link
