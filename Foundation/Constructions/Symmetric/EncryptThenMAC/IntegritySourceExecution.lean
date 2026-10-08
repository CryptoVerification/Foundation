import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityExecutionStage

/-! Every finite source instruction and adaptive signing interaction is
refined by an actual integrity-controller stage. Completion still requires
a real source stopping witness; bounded evaluation alone is insufficient. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem source_oracleCall_control (code : SourceCode) (control : SourceControl)
    (machine : Configuration) (request : List Bool)
    (h : CryptoOracle.Interactive.Reification.action code control = .oracleCall machine request) :
    control = .awaiting machine request := by
  cases control <;> simp only [CryptoOracle.Interactive.Reification.action, CryptoOracle.Interactive.transition] at h
  all_goals try (repeat' (split at h <;> try simp_all))
  all_goals try simp_all

def TagLength (oracle : State → Bool → PMF (State × List Bool)) (width : Nat) : Prop :=
  ∀ state ciphertext answer, answer ∈ (oracle state ciphertext).support → answer.2.length = width

noncomputable def logicalStep (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (frame : LogicalFrame State) : PMF (LogicalFrame State) :=
  if CryptoOracle.Interactive.Reification.terminal frame.control then PMF.pure frame
  else match CryptoOracle.Interactive.Reification.action code frame.control with
    | .deterministic next => PMF.pure { frame with control := next.control }
    | .random zero one => sampleBit.map (fun bit =>
        { frame with control := if bit then one.control else zero.control })
    | .oracleCall machine request => logicalQuery oracle key machine request frame

noncomputable def oneStage (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (hTags : TagLength oracle width) (frame : LogicalFrame State) :
    TimedExecution.Stage (step code oracle) (LogicalFrame.embed key) frame :=
  if ht : CryptoOracle.Interactive.Reification.terminal frame.control = true then
    TimedExecution.Stage.identity (step code oracle) (LogicalFrame.embed key) frame
  else
    have hr : CryptoOracle.Interactive.Reification.terminal frame.control = false := by simpa using ht
    match ha : CryptoOracle.Interactive.Reification.action code frame.control with
    | .deterministic next => deterministicStage code oracle key frame next hr ha
    | .random zero one => randomStage code oracle key frame zero one hr ha
    | .oracleCall machine request => by
        have hc := source_oracleCall_control code frame.control machine request ha
        have he : queryStart frame.used machine request frame.state frame.sourceTrace frame.signingTrace = frame := by
          cases frame
          simp_all [queryStart]
        exact he ▸ queryStage code oracle key frame.used machine request frame.state frame.sourceTrace frame.signingTrace
          width (fun answer h => hTags _ _ answer h)

theorem oneStage_budget (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (hTags : TagLength oracle width) (frame : LogicalFrame State) :
    (oneStage code oracle key width hTags frame).budget ≤ 5 * width + 36 := by
  unfold oneStage
  split
  · simp [TimedExecution.Stage.identity]
  · split
    · simp [deterministicStage]
    · simp [randomStage]
    · rename_i machine request ha
      have hc := source_oracleCall_control code frame.control machine request ha
      cases frame with
      | mk state used control sourceTrace signingTrace =>
          dsimp only at hc
          subst control
          change queryBudget used width + 1 ≤ 5 * width + 36
          have h := queryBudget_le used width
          omega

theorem oneStage_distribution (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (hTags : TagLength oracle width) (frame : LogicalFrame State) :
    (oneStage code oracle key width hTags frame).outcome.map Prod.fst = logicalStep code oracle key frame := by
  unfold oneStage
  split
  · rename_i ht
    simp [logicalStep, ht, TimedExecution.Stage.identity, PMF.pure_map]
  · rename_i ht
    simp only [logicalStep, ht, Bool.false_eq_true, ↓reduceIte]
    split
    · simp_all [deterministicStage, PMF.pure_map]
    · simp_all [randomStage, PMF.map_comp, Function.comp_def]
    · rename_i machine request ha
      have hc := source_oracleCall_control code frame.control machine request ha
      cases frame with
      | mk state used control sourceTrace signingTrace =>
          dsimp only at hc
          subst control
          exact queryStage_distribution code oracle key used machine request state sourceTrace signingTrace width _

/-- Full joint distribution law for arbitrary finite code and adaptive
signing. Both histories and the private used state are retained. -/
theorem source_execution (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (hTags : TagLength oracle width) (count : Nat) (start : LogicalFrame State)
    (hStops : ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count start).support,
      CryptoOracle.Interactive.Reification.terminal final.control = true)
    (horizon : Nat) (hBudget : count * (5 * width + 36) ≤ horizon) :
    eval code oracle horizon (LogicalFrame.embed key start) =
      (TimedExecution.eval (logicalStep code oracle key) count start).map (LogicalFrame.embed key) := by
  have hFinal : ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count start).support,
      step code oracle (LogicalFrame.embed key final) = PMF.pure (LogicalFrame.embed key final) := by
    intro final hFinal
    apply terminal_step code oracle (LogicalFrame.embed key final)
    exact hStops final hFinal
  exact TimedExecution.Stage.iterate_final_law (oneStage code oracle key width hTags)
    (5 * width + 36) (oneStage_budget code oracle key width hTags)
    (logicalStep code oracle key) (oneStage_distribution code oracle key width hTags) count start hFinal horizon hBudget

theorem source_haltsWithin (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (hTags : TagLength oracle width) (count : Nat) (start : LogicalFrame State)
    (hStops : ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count start).support,
      CryptoOracle.Interactive.Reification.terminal final.control = true) :
    HaltsWithin code oracle (LogicalFrame.embed key start) (count * (5 * width + 36)) := by
  intro final hFinal
  rw [source_execution code oracle key width hTags count start hStops _ (Nat.le_refl _),
    PMF.mem_support_map_iff] at hFinal
  obtain ⟨source, hSource, he⟩ := hFinal
  subst final
  exact hStops source hSource

def logicalInitial (state : State) (input : List Bool) : LogicalFrame State :=
  ⟨state, false, .running (Configuration.initial input), [], []⟩

def executionBudget (width count : Nat) : Nat := 3 + count * (5 * width + 36)

theorem initialized_source_execution (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (width : Nat) (hTags : TagLength oracle width) (count : Nat) (state : State) (input : List Bool)
    (hStops : ∀ key ∈ sampleBit.support,
      ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).support,
        CryptoOracle.Interactive.Reification.terminal final.control = true) :
    eval code oracle (executionBudget width count) (initial state input) =
      sampleBit.bind (fun key =>
        (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).map (LogicalFrame.embed key)) := by
  rw [executionBudget, initialization_continue]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext key hKey
  change eval code oracle (count * (5 * width + 36)) (LogicalFrame.embed key (logicalInitial state input)) = _
  exact source_execution code oracle key width hTags count (logicalInitial state input) (hStops key hKey) _ (Nat.le_refl _)

theorem initialized_source_haltsWithin (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (width : Nat) (hTags : TagLength oracle width) (count : Nat) (state : State) (input : List Bool)
    (hStops : ∀ key ∈ sampleBit.support,
      ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).support,
        CryptoOracle.Interactive.Reification.terminal final.control = true) :
    HaltsWithin code oracle (initial state input) (executionBudget width count) := by
  intro final hFinal
  rw [initialized_source_execution code oracle width hTags count state input hStops,
    PMF.mem_support_bind_iff] at hFinal
  obtain ⟨key, hKey, hMap⟩ := hFinal
  rw [PMF.mem_support_map_iff] at hMap
  obtain ⟨source, hSource, he⟩ := hMap
  subst final
  exact hStops key hKey source hSource

theorem execution_profile_polynomial {width count : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hCount : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n => executionBudget (width n) (count n)) :=
  (PolynomiallyBounded.const 3).add
    (hCount.mul (((PolynomiallyBounded.const 5).mul hWidth).add (PolynomiallyBounded.const 36)))

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
