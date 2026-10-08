import Foundation.Crypto.Semantics.Oracle.FreshMaskAdaptiveExecution
import Foundation.Crypto.Semantics.Oracle.FreshMaskAdaptiveRoundExactTime

/-! Joint full-result and cumulative cost for any number of native calls.
This is the composed certificate law. Identifying the whole execution's
first terminal arrival additionally requires excluding earlier termination. -/
namespace CryptoOracle.Interactive.FreshMaskAdaptiveExecution
open Machine Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
variable {State : Type u} (oracle : BitOracle State)

theorem whole_costed (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    (whole oracle rounds state past request trace).execution.costed () =
      (law rounds state past request trace).map
        (fun final => (final, timeBound rounds request.length)) := by
  induction rounds generalizing past request trace with
  | zero => simp [whole, finish, TimedExecution.Procedure.ofFixed, law, timeBound, PMF.pure_map]
  | succ rounds ih =>
      change (((FreshMaskAdaptiveRound.round oracle state rounds past request trace).costed ()).bind
        (fun first => ((whole oracle rounds state (some true :: past) first.1
          ((request, first.1) :: trace)).execution.costed ()).map
            (fun last => ((first.1, last.1), first.2 + last.2)))).map
              (fun result => (result.1.2, result.2)) = _
      rw [FreshMaskAdaptiveRound.round_costed, PMF.map_bind, PMF.bind_map]
      simp only [PMF.map_comp, Function.comp_def]
      rw [law, PMF.map_bind]
      congr 1
      funext ciphertext
      rw [ih, PMF.map_comp]
      congr 1
      funext final
      dsimp only [Function.comp_def]
      rw [Bits.length_toList]
      congr 1
      simp only [timeBound, Nat.add_mul, Nat.one_mul]
      omega

end CryptoOracle.Interactive.FreshMaskAdaptiveExecution
