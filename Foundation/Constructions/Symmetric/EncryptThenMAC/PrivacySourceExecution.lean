import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyExecutionStage

/-! Compose every possible source instruction and adaptive query. The
logical source frame is a proof coordinate, not an alternative runtime. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem oracleCall_control (code : Source.Code) (control : Source.Control)
    (machine : Configuration) (request : List Bool)
    (h : CryptoOracle.Interactive.Reification.action code control = .oracleCall machine request) :
    control = .awaiting machine request := by
  cases control <;> simp only [CryptoOracle.Interactive.Reification.action, CryptoOracle.Interactive.transition] at h
  all_goals try (repeat' (split at h <;> try simp_all))
  all_goals try simp_all

noncomputable def logicalStep {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (frame : LogicalFrame State) : PMF (LogicalFrame State) :=
  if CryptoOracle.Interactive.Reification.terminal frame.control then PMF.pure frame
  else match CryptoOracle.Interactive.Reification.action code frame.control with
    | .deterministic next => PMF.pure { frame with control := next.control }
    | .random zero one => sampleBit.map fun bit =>
        { frame with control := if bit then one.control else zero.control }
    | .oracleCall machine request => (oracle frame.state request).map fun answer =>
        queryResult key machine request answer frame.sourceTrace frame.externalTrace

noncomputable def oneStage {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (frame : LogicalFrame State) : TimedExecution.Stage (step code oracle) (LogicalFrame.embed key) frame :=
  if ht : CryptoOracle.Interactive.Reification.terminal frame.control = true then
    TimedExecution.Stage.identity (step code oracle) (LogicalFrame.embed key) frame
  else
    have hr : CryptoOracle.Interactive.Reification.terminal frame.control = false := by simpa using ht
    match ha : CryptoOracle.Interactive.Reification.action code frame.control with
    | .deterministic next => deterministicStage code oracle key frame next hr ha
    | .random zero one => randomStage code oracle key frame zero one hr ha
    | .oracleCall machine request => by
        have hc := oracleCall_control code frame.control machine request ha
        have he : queryStart machine request frame.state frame.layout frame.sourceTrace frame.externalTrace = frame := by
          cases frame
          simp_all [queryStart]
        exact he ▸ queryStage code oracle key machine request frame.state frame.layout frame.sourceTrace frame.externalTrace

theorem oneStage_budget {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width) (frame : LogicalFrame State) :
    (oneStage code oracle key frame).budget ≤ 29 * width + 39 := by
  unfold oneStage
  split
  · simp [TimedExecution.Stage.identity]
  · split
    · simp [deterministicStage]
    · simp [randomStage]
    · rename_i machine request ha
      have hc := oracleCall_control code frame.control machine request ha
      cases frame with
      | mk state layout control sourceTrace externalTrace =>
          dsimp only at hc
          subst control
          change 29 * width + 39 ≤ 29 * width + 39
          exact Nat.le_refl _

theorem oneStage_distribution {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width) (frame : LogicalFrame State) :
    (oneStage code oracle key frame).outcome.map Prod.fst = logicalStep code oracle key frame := by
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
      have hc := oracleCall_control code frame.control machine request ha
      cases frame with
      | mk state layout control sourceTrace externalTrace =>
          dsimp only at hc
          subst control
          exact queryStage_distribution code oracle key machine request state layout sourceTrace externalTrace

/-- Full joint execution law at a uniform native transition bound. Its
source stopping hypothesis is separate from the implementation proof. -/
theorem source_execution {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (count : Nat) (start : LogicalFrame State)
    (hStops : ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count start).support,
      CryptoOracle.Interactive.Reification.terminal final.control = true)
    (horizon : Nat) (hBudget : count * (29 * width + 39) ≤ horizon) :
    eval code oracle horizon (LogicalFrame.embed key start) =
      (TimedExecution.eval (logicalStep code oracle key) count start).map (LogicalFrame.embed key) := by
  have hFinal : ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count start).support,
      step code oracle (LogicalFrame.embed key final) = PMF.pure (LogicalFrame.embed key final) := by
    intro final hFinal
    apply step_terminal code oracle (LogicalFrame.embed key final)
    exact hStops final hFinal
  simpa only [Timing.eval_eq] using TimedExecution.Stage.iterate_final_law
    (oneStage code oracle key) (29 * width + 39) (oneStage_budget code oracle key)
    (logicalStep code oracle key) (oneStage_distribution code oracle key) count start hFinal horizon hBudget

theorem source_haltsWithin {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (count : Nat) (start : LogicalFrame State)
    (hStops : ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count start).support,
      CryptoOracle.Interactive.Reification.terminal final.control = true) :
    HaltsWithin code oracle (LogicalFrame.embed key start) (count * (29 * width + 39)) := by
  intro final hFinal
  rw [source_execution code oracle key count start hStops _ (Nat.le_refl _),
    PMF.mem_support_map_iff] at hFinal
  obtain ⟨source, hSource, he⟩ := hFinal
  subst final
  exact hStops source hSource

def logicalInitial {State : Type u} (state : State) (input : List Bool) : LogicalFrame State :=
  ⟨state, .generated, .running (Configuration.initial input), [], []⟩

def executionBudget (width count : Nat) : Nat := 12 * width + 5 + count * (29 * width + 39)

/-- The actual complete machine, starting before private key generation,
has the keygen-and-logical-source joint distribution at this transition bound. -/
theorem initialized_source_execution {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n count : Nat)
    (state : State) (input : List Bool)
    (hStops : ∀ key ∈ ((TableMAC.scheme width).keygen n).support,
      ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).support,
        CryptoOracle.Interactive.Reification.terminal final.control = true) :
    eval code oracle (executionBudget (width n) count)
      (initial state (List.replicate (2 * width n) true) input) =
      ((TableMAC.scheme width).keygen n).bind (fun key =>
        (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).map
          (LogicalFrame.embed key)) := by
  unfold executionBudget initial
  rw [initialization_then_run]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext key hKey
  exact source_execution code oracle key count (logicalInitial state input) (hStops key hKey)
    _ (Nat.le_refl _)

theorem initialized_source_haltsWithin {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n count : Nat)
    (state : State) (input : List Bool)
    (hStops : ∀ key ∈ ((TableMAC.scheme width).keygen n).support,
      ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).support,
        CryptoOracle.Interactive.Reification.terminal final.control = true) :
    HaltsWithin code oracle (initial state (List.replicate (2 * width n) true) input)
      (executionBudget (width n) count) := by
  intro final hFinal
  rw [initialized_source_execution code oracle width n count state input hStops,
    PMF.mem_support_bind_iff] at hFinal
  obtain ⟨key, hKey, hMap⟩ := hFinal
  rw [PMF.mem_support_map_iff] at hMap
  obtain ⟨source, hSource, he⟩ := hMap
  subst final
  exact hStops key hKey source hSource

theorem execution_profile_polynomial {width count : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hCount : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n => executionBudget (width n) (count n)) :=
  (((PolynomiallyBounded.const 12).mul hWidth).add (PolynomiallyBounded.const 5)).add
    (hCount.mul (((PolynomiallyBounded.const 29).mul hWidth).add (PolynomiallyBounded.const 39)))

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
