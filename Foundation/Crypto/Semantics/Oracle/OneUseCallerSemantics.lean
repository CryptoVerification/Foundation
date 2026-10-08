import Foundation.Crypto.Semantics.Oracle.OneUseProgress

/-! Caller-level semantics of the same finite code: ordinary transitions
remain unchanged, while a physically laid-out query is one logical operation.
Its native preparation/crypto/delivery cost is counted only by the existing
physical contract, not by this logical instruction counter. Invalid query
layouts remain stalled; they are not fabricated responses or halts. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool))

noncomputable def callerStep (source : Boundary State) : PMF (Boundary State) :=
  if OneUseSourceInterval.boundary code source.frame.control then
    (query code oracle key keyTail).semantics source
  else (Reification.timedStep code oracle source.frame).map (Boundary.mk source.spent)

def queryOperations (source : Boundary State) : Nat :=
  if OneUseSourceInterval.boundary code source.frame.control then 1 else 0

noncomputable def callerRound (fuel : Nat) (source : Boundary State) : PMF (Boundary State × Nat) :=
  ((caller code oracle key keyTail fuel).costed source).bind (fun first =>
    ((query code oracle key keyTail).semantics first.1).map
      (fun final => (final, first.2 + queryOperations code first.1)))

theorem queryAt_idle (source : Boundary State) (hNo : ¬ Nonempty (CallLayout code source.frame)) :
    (queryAt code oracle key keyTail source).semantics () = PMF.pure source := by
  rw [← (queryAt code oracle key keyTail source).correct, queryAt_no_layout code oracle key keyTail source hNo,
    PMF.pure_map]

theorem queryAt_before_boundary (source : Boundary State)
    (hb : OneUseSourceInterval.boundary code source.frame.control = false) :
    (queryAt code oracle key keyTail source).semantics () = PMF.pure source := by
  apply queryAt_idle
  rintro ⟨data⟩
  simp [OneUseSourceInterval.boundary, data.control, data.active, data.call] at hb

/-- Missing layout leaves the caller stalled at its existing frame. A
finite stopping proof cannot convert this state into a successful call. -/
theorem callerStep_stalled (source : Boundary State)
    (hb : OneUseSourceInterval.boundary code source.frame.control = true)
    (hNo : ¬ Nonempty (CallLayout code source.frame)) :
    callerStep code oracle key keyTail source = PMF.pure source := by
  simp only [callerStep, hb, ↓reduceIte]
  exact queryAt_idle code oracle key keyTail source hNo

theorem caller_stalled_run (source : Boundary State)
    (hb : OneUseSourceInterval.boundary code source.frame.control = true)
    (hNo : ¬ Nonempty (CallLayout code source.frame)) (bound : Nat) :
    TimedExecution.eval (callerStep code oracle key keyTail) bound source = PMF.pure source :=
  Block.eval_of_absorbing source (callerStep_stalled code oracle key keyTail source hb hNo) bound

theorem callerStep_call (source : Boundary State) (data : CallLayout code source.frame) :
    callerStep code oracle key keyTail source =
      PMF.pure (Boundary.mk (OneUseXorRequest.used source.spent key data.request)
        (NativeCallback.resumed data.machine.advance source.frame.state source.frame.reverseTrace
          data.request (OneUseXorRequest.reply source.spent key data.request))) := by
  have hb : OneUseSourceInterval.boundary code source.frame.control = true := by
    simp [OneUseSourceInterval.boundary, data.control, data.active, data.call]
  simp only [callerStep, hb, ↓reduceIte]
  exact queryAt_semantics code oracle key keyTail source data

theorem callerStep_halt (source : Boundary State) (machine : Machine.Configuration)
    (hControl : source.frame.control = .running machine) (hActive : machine.halted = false)
    (hHalt : code[machine.pc]? = some (.native .halt)) :
    callerStep code oracle key keyTail source =
      PMF.pure (Boundary.mk source.spent { source.frame with control := .running { machine with halted := true } }) := by
  simp [callerStep, OneUseSourceInterval.boundary, Reification.timedStep, Reification.terminal,
    Reification.perform, Reification.action, transition, hControl, hActive, hHalt,
    Machine.Instruction.next, PMF.pure_map]

theorem callerStep_terminal (source : Boundary State)
    (hTerminal : Reification.terminal source.frame.control = true) :
    callerStep code oracle key keyTail source = PMF.pure source := by
  have hb : OneUseSourceInterval.boundary code source.frame.control = true := by
    cases hc : source.frame.control <;> simp_all [OneUseSourceInterval.boundary, Reification.terminal]
  simp only [callerStep, hb, ↓reduceIte]
  exact queryAt_terminal code oracle key keyTail source hTerminal

theorem callerRound_marginal (stateSize : State → Nat) (fuel : Nat) (source : Boundary State) :
    (callerRound code oracle key keyTail fuel source).map Prod.fst =
      (automaticRound stateSize code oracle key keyTail fuel).semantics source := by
  rw [automaticRound_semantics]
  simp only [callerRound, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [← (caller code oracle key keyTail fuel).correct source, PMF.bind_map]
  congr 1
  funext first
  exact PMF.map_id _

theorem caller_reachable (fuel : Nat) (source : Boundary State) (result : Boundary State × Nat)
    (hResult : result ∈ ((caller code oracle key keyTail fuel).costed source).support) :
    result.1 ∈ (TimedExecution.eval (callerStep code oracle key keyTail) result.2 source).support := by
  rw [caller_costed, PMF.mem_support_map_iff] at hResult
  obtain ⟨returned, hr, he⟩ := hResult
  subst result
  have ht : (Boundary.mk source.spent returned.1, returned.2) ∈
      (runToBoundary (callerStep code oracle key keyTail)
        (fun s => OneUseSourceInterval.boundary code s.frame.control) fuel source).support := by
    rw [runToBoundary_map (Reification.timedStep code oracle) (callerStep code oracle key keyTail)
      (fun frame => OneUseSourceInterval.boundary code frame.control)
      (fun s => OneUseSourceInterval.boundary code s.frame.control) (Boundary.mk source.spent)
      (fun _ => rfl) (fun frame hb => by simp [callerStep, hb])]
    rw [PMF.mem_support_map_iff]
    exact ⟨returned, hr, rfl⟩
  exact runToBoundary_reachable _ _ fuel source _ ht

theorem query_reachable (source result : Boundary State)
    (hResult : result ∈ ((query code oracle key keyTail).semantics source).support) :
    result ∈ (TimedExecution.eval (callerStep code oracle key keyTail)
      (queryOperations code source) source).support := by
  cases hb : OneUseSourceInterval.boundary code source.frame.control with
  | true =>
      simpa [queryOperations, TimedExecution.eval, callerStep, hb, PMF.bind_pure] using hResult
  | false =>
      change result ∈ ((queryAt code oracle key keyTail source).semantics ()).support at hResult
      rw [queryAt_before_boundary code oracle key keyTail source hb, PMF.mem_support_pure_iff] at hResult
      subst result
      simp [queryOperations, hb, TimedExecution.eval]

theorem callerRound_reachable (fuel : Nat) (source : Boundary State) (result : Boundary State × Nat)
    (hResult : result ∈ (callerRound code oracle key keyTail fuel source).support) :
    result.1 ∈ (TimedExecution.eval (callerStep code oracle key keyTail) result.2 source).support := by
  rw [callerRound, PMF.mem_support_bind_iff] at hResult
  obtain ⟨first, hf, hs⟩ := hResult
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨final, hs, he⟩ := hs
  subst result
  rw [TimedExecution.eval_add, PMF.mem_support_bind_iff]
  exact ⟨first.1, caller_reachable code oracle key keyTail fuel source first hf,
    query_reachable code oracle key keyTail first.1 final hs⟩

theorem callerRound_positive (fuel : Nat) (hFuel : 0 < fuel) (source : Boundary State)
    (result : Boundary State × Nat) (hResult : result ∈ (callerRound code oracle key keyTail fuel source).support) :
    0 < result.2 := by
  rw [callerRound, PMF.mem_support_bind_iff] at hResult
  obtain ⟨first, hf, hs⟩ := hResult
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨final, _, he⟩ := hs
  subst result
  cases hb : OneUseSourceInterval.boundary code source.frame.control with
  | true =>
      rw [caller_costed_at_boundary code oracle key keyTail fuel source hb, PMF.mem_support_pure_iff] at hf
      subst first
      simp [queryOperations, hb]
  | false =>
      rw [caller_costed, PMF.mem_support_map_iff] at hf
      obtain ⟨returned, hr, he⟩ := hf
      subst first
      have hp := runToBoundary_progress (Reification.timedStep code oracle)
        (fun frame => OneUseSourceInterval.boundary code frame.control) fuel hFuel source.frame hb returned hr
      omega

end CryptoOracle.Interactive.OneUseSourceRounds
