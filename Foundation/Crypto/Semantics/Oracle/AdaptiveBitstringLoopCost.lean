import Foundation.Crypto.Semantics.Oracle.AdaptiveBitstringLoopExecution

/-! Exact adaptive cost law: query and reply lengths, oracle state, transcript
and actual accumulated duration remain correlated. Time caps certify support
only; they do not pad individual rounds or replace their actual durations. -/
namespace CryptoOracle.Interactive.AdaptiveBitstringLoop
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (oracle : BitOracle State) (cap : Nat)
    (hResponse : ∀ state request answer, answer ∈ (oracle state request).support → answer.2.length ≤ cap)

theorem round_costed (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (round oracle state remaining past request trace cap hResponse).costed () =
      (oracle state request).map (fun answer => (answer, 2 * request.length + 3 * answer.2.length + 9)) := by
  simp only [round, Procedure.observe, Procedure.seq, Procedure.andThen_costed,
    prepareRound, exchange, suffix, Procedure.ofFixed, PMF.pure_map, PMF.pure_bind,
    PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  congr 1
  funext answer
  congr 1
  dsimp only
  congr 1
  omega

noncomputable def costLaw : Nat → State → List (Option Bool) → List Bool → List (List Bool × List Bool) → PMF (Configuration State × Nat)
  | 0, state, past, request, trace => PMF.pure (finished state past request trace, 2)
  | rounds + 1, state, past, request, trace => (oracle state request).bind fun answer =>
      (costLaw rounds answer.1 (some true :: past) answer.2 ((request, answer.2) :: trace)).map
        (fun result => (result.1, 2 * request.length + 3 * answer.2.length + 9 + result.2))

theorem whole_costed (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (whole oracle cap hResponse rounds state past request trace).execution.costed () =
      costLaw oracle rounds state past request trace := by
  induction rounds generalizing state past request trace with
  | zero => simp [whole, finish, costLaw, Procedure.withBudget, Procedure.ofFixed, PMF.pure_map]
  | succ rounds ih =>
      change (((round oracle state rounds past request trace cap hResponse).costed ()).bind (fun first =>
        ((whole oracle cap hResponse rounds first.1.1 (some true :: past) first.1.2 ((request, first.1.2) :: trace)).execution.costed ()).map
          (fun second => ((first.1, second.1), first.2 + second.2)))).map (fun result => (result.1.2, result.2)) = _
      rw [round_costed]
      simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, costLaw]
      congr 1
      funext answer
      rw [ih]

end CryptoOracle.Interactive.AdaptiveBitstringLoop
