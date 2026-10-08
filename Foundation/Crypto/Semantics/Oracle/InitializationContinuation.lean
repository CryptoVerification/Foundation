import Foundation.Crypto.Semantics.Oracle.OneUseInitialization
import Foundation.Crypto.Semantics.InitializedContinuation

/-! Compose any actual private initialization contract with its consumer.
The generated physical store must equal the consumer's expected store.
Both actual cost distributions and the unchanged residual runtime survive. -/
namespace CryptoOracle.Interactive.OneUseInitialization
open Foundation.Probability TimedExecution
universe u v w x y
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {Key : Type w} {Output : Type x}
    (generator native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Configuration State)
    (init : Procedure (step generator native code oracle caller) Input (Key × Unit))
    (store : Key → Machine.Tape)
    (hExit : ∀ input result, result ∈ (init.semantics input).support →
      init.exit input result = .active (.source false (store result.1) caller))
    (continuation : Procedure (OneUseSource.step native code oracle) Key Output)
    (hEntry : ∀ key, continuation.entry key = .source false (store key) caller)
    (cap : Input → Nat)
    (hCap : ∀ input result, result ∈ (init.semantics input).support →
      continuation.budget result.1 ≤ cap input)

noncomputable def follow :=
  init.seq
    ((continuation.transport (step generator native code oracle caller) Control.active (fun _ => rfl)).reindex Prod.fst)
    (fun input result h => (congrArg Control.active (hEntry result.1)).trans (hExit input result h).symm)
    cap hCap

theorem follow_budget (input : Input) :
    (follow generator native code oracle caller init store hExit continuation hEntry cap hCap).budget input =
      init.budget input + cap input := rfl

theorem follow_costed (input : Input) :
    (follow generator native code oracle caller init store hExit continuation hEntry cap hCap).costed input =
      (init.costed input).bind (fun first => (continuation.costed first.1.1).map
        (fun second => ((first.1, second.1), first.2 + second.2))) := rfl

theorem follow_semantics (input : Input) :
    (follow generator native code oracle caller init store hExit continuation hEntry cap hCap).semantics input =
      (init.semantics input).bind (fun first => (continuation.semantics first.1).map
        (fun second => (first, second))) := rfl

/-- Project the actual key/generation-time joint distribution, retaining
possible correlations. A key marginal alone is not a timing certificate. -/
theorem follow_public_cost {Observed : Type y} (input : Input)
    (keyCost : PMF (Key × Nat))
    (hGenerated : (init.costed input).map (fun result => (result.1.1, result.2)) = keyCost)
    (view : Key → Output → Observed) :
    ((follow generator native code oracle caller init store hExit continuation hEntry cap hCap).costed input).map
      (fun result => (view result.1.1.1 result.1.2, result.2)) =
      keyCost.bind (fun first => (continuation.costed first.1).map
        (fun second => (view first.1 second.1, first.2 + second.2))) := by
  rw [follow_costed, ← hGenerated]
  simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

/-- Apply timing-conditioned security to the actual physically composed
initialization and consumer, retaining their total cost distribution. -/
theorem follow_public_cost_by_time {Observed : Type y} (input : Input)
    (times : PMF Nat) (keysAt : Nat → PMF Key)
    (hGenerated : (init.costed input).map (fun result => (result.1.1, result.2)) =
      times.bind (fun time => (keysAt time).map (fun key => (key, time))))
    (view : Key → Output → Observed) (commonSuffix : Nat → PMF (Observed × Nat))
    (hSuffix : ∀ time, (keysAt time).bind (fun key => (continuation.costed key).map
      (fun result => (view key result.1, result.2))) = commonSuffix time) :
    ((follow generator native code oracle caller init store hExit continuation hEntry cap hCap).costed input).map
      (fun result => (view result.1.1.1 result.1.2, result.2)) =
      times.bind (fun time => (commonSuffix time).map
        (fun result => (result.1, time + result.2))) := by
  rw [follow_public_cost generator native code oracle caller init store hExit continuation hEntry cap hCap
    input _ hGenerated view]
  have h := InitializedContinuation.compose_by_time
    (times.bind (fun time => (keysAt time).map (fun key => (key, time))))
    (fun key => (continuation.costed key).map (fun result => (view key result.1, result.2)))
    times keysAt commonSuffix rfl hSuffix
  simpa only [InitializedContinuation.compose, PMF.map_comp, Function.comp_def] using h

/-- A key-independent consumer adds no key-dependent public behavior to
initialization. Any key/timing correlation of the initializer is retained. -/
theorem follow_public_cost_independent {Observed : Type y} (input : Input)
    (view : Key → Output → Observed) (common : PMF (Observed × Nat))
    (hConsumer : ∀ key, (continuation.costed key).map
      (fun result => (view key result.1, result.2)) = common) :
    ((follow generator native code oracle caller init store hExit continuation hEntry cap hCap).costed input).map
      (fun result => (view result.1.1.1 result.1.2, result.2)) =
      ((init.costed input).map Prod.snd).bind (fun time => common.map
        (fun result => (result.1, time + result.2))) := by
  rw [follow_costed]
  simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  congr 1
  funext first
  have h := congrArg (fun distribution => distribution.map
    (fun result => (result.1, first.2 + result.2))) (hConsumer first.1.1)
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- Discarding timing, the actual generated key and a key-independent
public consumer result factor. No independence of generation time is used. -/
theorem follow_key_public_result {Observed : Type y} (input : Input)
    (prior : PMF Key)
    (hGenerated : (init.semantics input).map Prod.fst = prior)
    (view : Key → Output → Observed) (common : PMF Observed)
    (hConsumer : ∀ key, (continuation.semantics key).map (view key) = common) :
    ((follow generator native code oracle caller init store hExit continuation hEntry cap hCap).semantics input).map
      (fun result => (result.1.1, view result.1.1 result.2)) =
      prior.bind (fun key => common.map (fun output => (key, output))) := by
  rw [follow_semantics, ← hGenerated]
  simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  congr 1
  funext first
  have h := congrArg (fun distribution => distribution.map (fun output => (first.1, output)))
    (hConsumer first.1)
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- No fixed generation time, uniformity, or absorbing continuation is
assumed. Remaining time runs the original initialization/runtime system. -/
theorem follow_resume_law (input : Input) (horizon : Nat)
    (hBudget : init.budget input + cap input ≤ horizon) :
    TimedExecution.eval (step generator native code oracle caller) horizon (init.entry input) =
      ((follow generator native code oracle caller init store hExit continuation hEntry cap hCap).costed input).bind
        (fun result => TimedExecution.eval (step generator native code oracle caller) (horizon - result.2)
          (.active (continuation.exit result.1.1.1 result.1.2))) :=
  (follow generator native code oracle caller init store hExit continuation hEntry cap hCap).law input horizon hBudget

end CryptoOracle.Interactive.OneUseInitialization
