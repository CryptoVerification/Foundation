import Foundation.Crypto.Semantics.Oracle.ResponseLoading
import Foundation.Crypto.Semantics.ExecutionStage
import Foundation.Crypto.Semantics.Oracle.RequestExport

/-! A real source oracle call followed by cell-level response loading and
source resumption. Oracle-internal computation is separate from controller
costs. This contract starts after the request has actually been exported. -/
namespace CryptoOracle.Interactive.QueryTransfer
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : Code) (oracle : BitOracle State)

def awaiting (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) : Configuration State :=
  ⟨state, .awaiting machine request, trace⟩

def resumed (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (request : List Bool) (answer : State × List Bool) : Configuration State :=
  ⟨answer.1, .running { machine with outputTape := ResponseLoading.loaded answer.2 },
    (request, answer.2) :: trace⟩

noncomputable def stage (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (cap : Nat)
    (hLength : ∀ answer ∈ (oracle state request).support, answer.2.length ≤ cap) :
    Stage (Reification.timedStep code oracle) id (awaiting machine state trace request) where
  budget := 3 * cap + 3
  outcome := (oracle state request).map (fun answer =>
    (resumed machine trace request answer, 3 * answer.2.length + 3))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨answer, hAnswer, he⟩ := hResult
    subst result
    have h := hLength answer hAnswer
    omega
  law := by
    intro horizon hHorizon
    cases horizon with
    | zero => omega
    | succ fuel =>
        simp only [TimedExecution.eval, awaiting, Reification.timedStep, Reification.terminal,
          Bool.false_eq_true, ↓reduceIte, Reification.perform, Reification.action,
          transition, PMF.bind_map, Function.comp_def, id_eq]
        rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
        congr 1
        funext answer hAnswer
        have h := hLength answer hAnswer
        have hc := ResponseLoading.continues code oracle machine answer.1
          ((request, answer.2) :: trace) answer.2 fuel (by omega)
        simpa only [resumed, show fuel + 1 - (3 * answer.2.length + 3) =
          fuel - (3 * answer.2.length + 2) by omega] using hc

theorem distribution (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (cap : Nat)
    (hLength : ∀ answer ∈ (oracle state request).support, answer.2.length ≤ cap) :
    (stage code oracle machine state trace request cap hLength).outcome.map Prod.fst =
      (oracle state request).map (resumed machine trace request) := by
  simp only [stage, PMF.map_comp, Function.comp_def]

theorem call_export (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request) :
    TimedExecution.eval (Reification.timedStep code oracle) (2 * request.length + 3)
      (⟨state, .running machine, trace⟩ : Configuration State) =
    PMF.pure (awaiting machine.advance state trace request) := by
  rw [show 2 * request.length + 3 = (2 * request.length + 2) + 1 by omega, TimedExecution.eval]
  simp only [Reification.timedStep, Reification.terminal, hActive, Bool.false_eq_true,
    ↓reduceIte, Reification.perform, Reification.action, transition, hCall, PMF.pure_bind]
  rw [hTape]
  exact RequestExport.run code oracle machine.advance state trace request before after

/-- A complete real source call: capture, request export, external query,
response writing, rewind and resumption. Only oracle-internal work is external.
The request comes from the displayed physical tape, not a host-built packet. -/
noncomputable def fullStage (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request)
    (cap : Nat) (hLength : ∀ answer ∈ (oracle state request).support, answer.2.length ≤ cap) :
    Stage (Reification.timedStep code oracle) id
      (⟨state, .running machine, trace⟩ : Configuration State) where
  budget := (2 * request.length + 3) + (3 * cap + 3)
  outcome := (stage code oracle machine.advance state trace request cap hLength).outcome.map
    (fun result => (result.1, (2 * request.length + 3) + result.2))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨source, hSource, he⟩ := hResult
    subst result
    have h := (stage code oracle machine.advance state trace request cap hLength).bounded source hSource
    change source.2 ≤ 3 * cap + 3 at h
    omega
  law := by
    intro horizon hHorizon
    change TimedExecution.eval (Reification.timedStep code oracle) horizon
      (⟨state, .running machine, trace⟩ : Configuration State) = _
    conv_lhs => rw [show horizon = (2 * request.length + 3) + (horizon - (2 * request.length + 3)) by omega,
      TimedExecution.eval_add, call_export code oracle machine state trace request before after hActive hCall hTape,
      PMF.pure_bind]
    have h := (stage code oracle machine.advance state trace request cap hLength).law
      (horizon - (2 * request.length + 3)) (by change 3 * cap + 3 ≤ _; omega)
    rw [PMF.bind_map]
    simpa only [Nat.sub_sub, Nat.add_comm, Function.comp_def, id_eq] using h

end CryptoOracle.Interactive.QueryTransfer
