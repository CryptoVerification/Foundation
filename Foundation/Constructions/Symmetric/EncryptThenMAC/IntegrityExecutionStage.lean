import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityInitialization
import Foundation.Crypto.Semantics.ExecutionStage

/-! Source coordinates and actual execution stages for integrity. The
coordinate retains encryption state and both histories; it is not runtime
code and cannot expose hidden state to the source instruction selector. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

structure LogicalFrame (State : Type u) where
  state : State
  used : Bool
  control : SourceControl
  sourceTrace : List (List Bool × List Bool) := []
  signingTrace : List (Bool × List Bool) := []

def LogicalFrame.embed (key : Bool) (frame : LogicalFrame State) : Frame State :=
  ⟨frame.state, .source key frame.used frame.control, frame.sourceTrace, frame.signingTrace⟩

def queryStart (used : Bool) (machine : Configuration) (request : List Bool)
    (state : State) (sourceTrace : List (List Bool × List Bool))
    (signingTrace : List (Bool × List Bool)) : LogicalFrame State :=
  ⟨state, used, .awaiting machine request, sourceTrace, signingTrace⟩

noncomputable def logicalQuery (oracle : State → Bool → PMF (State × List Bool)) (key : Bool)
    (machine : Configuration) (request : List Bool) (start : LogicalFrame State) : PMF (LogicalFrame State) :=
  if start.used then PMF.pure ⟨start.state, true, .loading machine [false] {},
    (request, [false]) :: start.sourceTrace, start.signingTrace⟩
  else (oracle start.state (Bool.xor key (request.headD false))).map (fun answer =>
    let ciphertext := Bool.xor key (request.headD false)
    let response := true :: ciphertext :: answer.2
    ⟨answer.1, true, .loading machine response {}, (request, response) :: start.sourceTrace,
      (ciphertext, answer.2) :: start.signingTrace⟩)

theorem logicalQuery_embed (oracle : State → Bool → PMF (State × List Bool)) (key : Bool)
    (machine : Configuration) (request : List Bool) (start : LogicalFrame State) :
    (logicalQuery oracle key machine request start).map (LogicalFrame.embed key) =
      queryResult start.used key machine request start.state start.sourceTrace start.signingTrace oracle := by
  cases hu : start.used with
  | false =>
      simp [logicalQuery, queryResult, LogicalFrame.embed, hu, PMF.map_comp, Function.comp_def]
      congr 1
      funext answer
      simp [signedResult, resumed]
  | true =>
      simp [logicalQuery, queryResult, hu, PMF.pure_map]
      rfl

noncomputable def queryStage (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key used : Bool) (machine : Configuration) (request : List Bool) (state : State)
    (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool)) (width : Nat)
    (hTags : ∀ answer ∈ (oracle state (Bool.xor key (request.headD false))).support, answer.2.length = width) :
    TimedExecution.Stage (step code oracle) (LogicalFrame.embed key)
      (queryStart used machine request state sourceTrace signingTrace) where
  budget := queryBudget used width + 1
  outcome := (logicalQuery oracle key machine request (queryStart used machine request state sourceTrace signingTrace)).map
    (fun frame => (frame, queryBudget used width + 1))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨frame, _, he⟩ := hResult
    subst result
    exact Nat.le_refl _
  law := by
    intro horizon hHorizon
    have hh : horizon = (queryBudget used width + 1) + (horizon - (queryBudget used width + 1)) := by omega
    change eval code oracle horizon (LogicalFrame.embed key (queryStart used machine request state sourceTrace signingTrace)) = _
    rw [hh, eval_add]
    change (eval code oracle (queryBudget used width + 1)
      ⟨state, .source key used (.awaiting machine request), sourceTrace, signingTrace⟩).bind _ = _
    rw [awaiting_query_run code oracle key machine request state sourceTrace signingTrace used width hTags]
    have he := logicalQuery_embed oracle key machine request (queryStart used machine request state sourceTrace signingTrace)
    simp only [queryStart] at he
    rw [← he, PMF.bind_map, PMF.bind_map]
    simp [Function.comp_def]
    rfl

theorem queryStage_distribution (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key used : Bool) (machine : Configuration) (request : List Bool) (state : State)
    (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool)) (width : Nat)
    (hTags : ∀ answer ∈ (oracle state (Bool.xor key (request.headD false))).support, answer.2.length = width) :
    (queryStage code oracle key used machine request state sourceTrace signingTrace width hTags).outcome.map Prod.fst =
      logicalQuery oracle key machine request (queryStart used machine request state sourceTrace signingTrace) := by
  simp only [queryStage, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

noncomputable def deterministicStage (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (start : LogicalFrame State) (next : CryptoOracle.Interactive.Configuration Unit)
    (hRunning : CryptoOracle.Interactive.Reification.terminal start.control = false)
    (hNext : CryptoOracle.Interactive.Reification.action code start.control = .deterministic next) :
    TimedExecution.Stage (step code oracle) (LogicalFrame.embed key) start where
  budget := 1
  outcome := PMF.pure ({ start with control := next.control }, 1)
  bounded := by intro result h; simp only [PMF.mem_support_pure_iff] at h; subst result; exact Nat.le_refl _
  law := by
    intro horizon hHorizon
    have hh : horizon = (horizon - 1) + 1 := by omega
    change eval code oracle horizon (LogicalFrame.embed key start) = _
    rw [hh, eval_succ]
    simp [step, transition, LogicalFrame.embed, hRunning, hNext, PMF.pure_bind]
    rfl

noncomputable def randomStage (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (start : LogicalFrame State) (zero one : CryptoOracle.Interactive.Configuration Unit)
    (hRunning : CryptoOracle.Interactive.Reification.terminal start.control = false)
    (hNext : CryptoOracle.Interactive.Reification.action code start.control = .random zero one) :
    TimedExecution.Stage (step code oracle) (LogicalFrame.embed key) start where
  budget := 1
  outcome := sampleBit.map (fun bit => ({ start with control := if bit then one.control else zero.control }, 1))
  bounded := by
    intro result h
    rw [PMF.mem_support_map_iff] at h
    obtain ⟨bit, _, he⟩ := h
    subst result
    exact Nat.le_refl _
  law := by
    intro horizon hHorizon
    have hh : horizon = (horizon - 1) + 1 := by omega
    change eval code oracle horizon (LogicalFrame.embed key start) = _
    rw [hh, eval_succ]
    simp only [step, transition, LogicalFrame.embed, hRunning, Bool.false_eq_true, ↓reduceIte, hNext, PMF.bind_map]
    congr 1
    funext bit
    cases bit <;> rfl

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
