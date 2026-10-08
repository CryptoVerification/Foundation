import Foundation.Crypto.Semantics.ExecutionStage
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyRepeatedCallback

/-! Proof-level source coordinates for composing arbitrary source-machine
steps. The runtime controller remains PrivacyMachine.step. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability
universe u
set_option backward.isDefEq.respectTransparency false

structure LogicalFrame (State : Type u) where
  state : State
  layout : StoreLayout
  control : Source.Control
  sourceTrace : List (List Bool × List Bool)
  externalTrace : List (List Bool × List Bool)

def LogicalFrame.embed {State : Type u} {width : Nat} (key : TableMAC.Key width)
    (frame : LogicalFrame State) : Frame State :=
  ⟨frame.state, .source (frame.layout.tape key) frame.control, frame.sourceTrace, frame.externalTrace⟩

def queryStart {State : Type u} (machine : Configuration) (request : List Bool) (state : State)
    (layout : StoreLayout) (sourceTrace externalTrace : List (List Bool × List Bool)) : LogicalFrame State :=
  ⟨state, layout, .awaiting machine request, sourceTrace, externalTrace⟩

def queryResult {State : Type u} {width : Nat} (key : TableMAC.Key width)
    (machine : Configuration) (request : List Bool) (answer : State × List Bool)
    (sourceTrace externalTrace : List (List Bool × List Bool)) : LogicalFrame State :=
  ⟨answer.1, .retained, .loading machine
    (AuthenticateResponse.encode ((decodeCiphertext answer.2).map (fun bit => (bit, TableMAC.sign key bit)))) {},
    (request, AuthenticateResponse.encode ((decodeCiphertext answer.2).map (fun bit => (bit, TableMAC.sign key bit)))) :: sourceTrace,
    (request, answer.2) :: externalTrace⟩

/-- A real external query followed by its real native callback, expressed
in source coordinates so that the next source step can be composed directly. -/
noncomputable def queryStage {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (machine : Configuration) (request : List Bool) (state : State) (layout : StoreLayout)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    TimedExecution.Stage (step code oracle) (LogicalFrame.embed key)
      (queryStart machine request state layout sourceTrace externalTrace) where
  budget := 29 * width + 39
  outcome := (oracle state request).bind (fun answer =>
    (storedCallback code oracle machine request answer.1 sourceTrace ((request, answer.2) :: externalTrace)
      layout key (decodeCiphertext answer.2)).outcome.map (fun result =>
        (queryResult key machine request answer sourceTrace externalTrace, result.2 + 1)))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_bind_iff] at hResult
    obtain ⟨answer, _, hMap⟩ := hResult
    rw [PMF.mem_support_map_iff] at hMap
    obtain ⟨callback, hCallback, he⟩ := hMap
    subst result
    have hb := storedCallback_bounded code oracle machine request answer.1 sourceTrace
      ((request, answer.2) :: externalTrace) layout key (decodeCiphertext answer.2) callback hCallback
    omega
  law := by
    intro horizon hHorizon
    rw [Timing.eval_eq]
    change eval code oracle horizon
      ⟨state, .source (layout.tape key) (.awaiting machine request), sourceTrace, externalTrace⟩ = _
    have hh : horizon = 1 + (horizon - 1) := by omega
    conv_lhs => rw [hh, stored_query_law code oracle machine request state sourceTrace externalTrace
      layout key (horizon - 1) (by omega)]
    rw [PMF.bind_bind]
    simp only [PMF.bind_map, Function.comp_def]
    congr 1
    funext answer
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext callback hCallback
    have he := storedCallback_endpoint code oracle machine request answer.1 sourceTrace
      ((request, answer.2) :: externalTrace) layout key (decodeCiphertext answer.2) callback hCallback
    rw [he, Timing.eval_eq]
    have ht : horizon - 1 - callback.2 = horizon - (callback.2 + 1) := by omega
    rw [ht]
    rfl

noncomputable def deterministicStage {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (frame : LogicalFrame State) (next : CryptoOracle.Interactive.Configuration Unit)
    (hRunning : CryptoOracle.Interactive.Reification.terminal frame.control = false)
    (hAction : CryptoOracle.Interactive.Reification.action code frame.control = .deterministic next) :
    TimedExecution.Stage (step code oracle) (LogicalFrame.embed key) frame where
  budget := 1
  outcome := PMF.pure ({ frame with control := next.control }, 1)
  bounded := by intro result h; simp only [PMF.mem_support_pure_iff] at h; subst result; exact Nat.le_refl _
  law := by
    intro horizon hHorizon
    cases horizon with
    | zero => omega
    | succ horizon =>
        rw [TimedExecution.eval, PMF.pure_bind]
        change (step code oracle ⟨frame.state, .source (frame.layout.tape key) frame.control,
          frame.sourceTrace, frame.externalTrace⟩).bind _ = _
        rw [source_deterministic code oracle _ _ _ _ _ next hRunning hAction, PMF.pure_bind]
        rfl

noncomputable def randomStage {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (frame : LogicalFrame State) (zero one : CryptoOracle.Interactive.Configuration Unit)
    (hRunning : CryptoOracle.Interactive.Reification.terminal frame.control = false)
    (hAction : CryptoOracle.Interactive.Reification.action code frame.control = .random zero one) :
    TimedExecution.Stage (step code oracle) (LogicalFrame.embed key) frame where
  budget := 1
  outcome := sampleBit.map (fun bit =>
    ({ frame with control := if bit then one.control else zero.control }, 1))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨bit, _, he⟩ := hResult
    subst result
    exact Nat.le_refl _
  law := by
    intro horizon hHorizon
    cases horizon with
    | zero => omega
    | succ horizon =>
        rw [TimedExecution.eval, PMF.bind_map]
        change (step code oracle ⟨frame.state, .source (frame.layout.tape key) frame.control,
          frame.sourceTrace, frame.externalTrace⟩).bind _ = _
        rw [source_random code oracle _ _ _ _ _ zero one hRunning hAction, PMF.bind_map]
        congr 1

/-- The source-state distribution is exactly an authenticated external
query with both transcripts retained. Its actual native duration is separate. -/
theorem queryStage_distribution {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (machine : Configuration) (request : List Bool) (state : State) (layout : StoreLayout)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    (queryStage code oracle key machine request state layout sourceTrace externalTrace).outcome.map Prod.fst =
      (oracle state request).map (fun answer => queryResult key machine request answer sourceTrace externalTrace) := by
  simp only [queryStage, PMF.map_bind, PMF.map_comp, Function.comp_def]
  conv_rhs => rw [PMF.map]
  congr 1
  funext answer
  exact PMF.map_const _ _

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
