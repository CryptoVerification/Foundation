import Foundation.Crypto.Semantics.Oracle.Program
import Foundation.Crypto.Semantics.Probability.Coupling

/-! An explicit joint execution of the same adaptive program against two
state types. Local coins are shared while answers agree. After different
answers the two continuations run independently. Both whole-outcome marginals
are proved; no agreement or small failure probability is assumed. -/
namespace CryptoOracle.Program

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Request Response Result LeftState RightState : Type} [DecidableEq Response]

/-- An independent joint law, used only after the continuations diverge. -/
noncomputable def independentRuns {Left Right : Type} (left : PMF Left) (right : PMF Right) :
    PMF (Left × Right) := left.bind fun value => right.map (value, ·)

@[simp] theorem independentRuns_left {Left Right : Type} (left : PMF Left) (right : PMF Right) :
    (independentRuns left right).map Prod.fst = left := by
  simp only [independentRuns, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (left.bind fun value => right.map (Function.const Right value)) = left
  simp only [PMF.map_const, PMF.bind_pure]

@[simp] theorem independentRuns_right {Left Right : Type} (left : PMF Left) (right : PMF Right) :
    (independentRuns left right).map Prod.snd = right := by
  simp only [independentRuns, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (left.bind fun _ => right.map id) = right
  rw [PMF.bind_const, PMF.map_id]

/-- Couple the attacker coins until a response differs. At queries the two
kernels are sampled independently; for deterministic kernels this is their
unique joint answer. This definition retains both complete public traces. -/
noncomputable def coupledRun (left : Oracle Request Response LeftState)
    (right : Oracle Request Response RightState) (leftState : LeftState) (rightState : RightState) :
    Program Request Response Result →
      PMF (Outcome Request Response Result LeftState × Outcome Request Response Result RightState)
  | .done result => PMF.pure (⟨result, leftState, []⟩, ⟨result, rightState, []⟩)
  | .coin next => sampleBit.bind fun bit => coupledRun left right leftState rightState (next bit)
  | .query request next =>
      (left leftState request).bind fun answerLeft =>
        (right rightState request).bind fun answerRight =>
          (if answerLeft.2 = answerRight.2 then
            coupledRun left right answerLeft.1 answerRight.1 (next answerLeft.2)
          else independentRuns (run left answerLeft.1 (next answerLeft.2))
            (run right answerRight.1 (next answerRight.2))).map fun pair =>
              ({ pair.1 with trace := (request, answerLeft.2) :: pair.1.trace },
               { pair.2 with trace := (request, answerRight.2) :: pair.2.trace })

/-- Exact marginals hold without any good-state or deterministic-kernel
hypothesis, including when the two attacker continuations have diverged. -/
theorem coupledRun_marginals (left : Oracle Request Response LeftState)
    (right : Oracle Request Response RightState) (program : Program Request Response Result)
    (leftState : LeftState) (rightState : RightState) :
    (coupledRun left right leftState rightState program).map Prod.fst = program.run left leftState ∧
    (coupledRun left right leftState rightState program).map Prod.snd = program.run right rightState := by
  induction program generalizing leftState rightState with
  | done result => simp [coupledRun, run, PMF.pure_map]
  | coin next ih =>
      constructor <;> simp only [coupledRun, run, PMF.map_bind]
      · congr 1; funext bit; exact (ih bit leftState rightState).1
      · congr 1; funext bit; exact (ih bit leftState rightState).2
  | query request next ih =>
      have tails (answerLeft : LeftState × Response) (answerRight : RightState × Response) :
          (if answerLeft.2 = answerRight.2 then
            coupledRun left right answerLeft.1 answerRight.1 (next answerLeft.2)
          else independentRuns (run left answerLeft.1 (next answerLeft.2))
            (run right answerRight.1 (next answerRight.2))).map Prod.fst =
              run left answerLeft.1 (next answerLeft.2) ∧
          (if answerLeft.2 = answerRight.2 then
            coupledRun left right answerLeft.1 answerRight.1 (next answerLeft.2)
          else independentRuns (run left answerLeft.1 (next answerLeft.2))
            (run right answerRight.1 (next answerRight.2))).map Prod.snd =
              run right answerRight.1 (next answerRight.2) := by
        by_cases same : answerLeft.2 = answerRight.2
        · simp only [if_pos same]
          exact ⟨(ih answerLeft.2 answerLeft.1 answerRight.1).1,
            (ih answerLeft.2 answerLeft.1 answerRight.1).2.trans (by rw [same])⟩
        · simp [same]
      constructor
      · simp only [coupledRun, PMF.map_bind, PMF.map_comp, Function.comp_def, run]
        congr 1
        funext answerLeft
        have mapped (answerRight : RightState × Response) := congrArg
          (PMF.map (fun out : Outcome Request Response Result LeftState =>
            { out with trace := (request, answerLeft.2) :: out.trace })) (tails answerLeft answerRight).1
        simp only [PMF.map_comp, Function.comp_def] at mapped
        simp_rw [mapped]
        simp
      · simp only [coupledRun, PMF.map_bind, PMF.map_comp, Function.comp_def, run]
        have mapped (answerLeft : LeftState × Response) (answerRight : RightState × Response) := congrArg
          (PMF.map (fun out : Outcome Request Response Result RightState =>
            { out with trace := (request, answerRight.2) :: out.trace })) (tails answerLeft answerRight).2
        simp only [PMF.map_comp, Function.comp_def] at mapped
        simp_rw [mapped]
        simp

/-- Identical public traces imply identical results in this explicit coupling.
This uses shared local coins before divergence, not a claim that an arbitrary
program's result is determined by its query trace. -/
theorem coupledRun_result_eq_of_trace_eq (left : Oracle Request Response LeftState)
    (right : Oracle Request Response RightState) (program : Program Request Response Result)
    (leftState : LeftState) (rightState : RightState)
    (pair : Outcome Request Response Result LeftState × Outcome Request Response Result RightState)
    (support : pair ∈ (coupledRun left right leftState rightState program).support)
    (traces : pair.1.trace = pair.2.trace) : pair.1.result = pair.2.result := by
  induction program generalizing leftState rightState pair with
  | done result =>
      simp only [coupledRun, PMF.mem_support_pure_iff] at support
      subst pair
      rfl
  | coin next ih =>
      rw [coupledRun, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, reachable⟩ := support
      exact ih bit leftState rightState pair reachable traces
  | query request next ih =>
      rw [coupledRun, PMF.mem_support_bind_iff] at support
      obtain ⟨answerLeft, _, support⟩ := support
      rw [PMF.mem_support_bind_iff] at support
      obtain ⟨answerRight, _, support⟩ := support
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨tail, reachable, rfl⟩ := support
      have same : answerLeft.2 = answerRight.2 :=
        congrArg Prod.snd (List.cons.inj traces).1
      rw [if_pos same] at reachable
      exact ih answerLeft.2 answerLeft.1 answerRight.1 tail reachable (List.cons.inj traces).2

end CryptoOracle.Program
