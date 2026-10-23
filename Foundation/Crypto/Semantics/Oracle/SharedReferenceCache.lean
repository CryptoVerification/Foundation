import Foundation.Crypto.Semantics.Oracle.SharedReference
import Foundation.Crypto.Semantics.Oracle.RandomOracle
import Foundation.Crypto.Semantics.Probability.Copyability

/-! Two aliases use the SAME updated lazy cache. The first read inserts one
entry and the second returns it. Resetting to a fresh cache for each read is
a different computation. The reset example is a diagnostic program, not a
replacement of the existing MAC controller. -/
namespace CryptoOracle.SharedReference
open Foundation.Probability
variable {Input Response : Type} [DecidableEq Input] [Fintype Response] [Nonempty Response]

def readPair (one two : Ref) (input : Input) : Program (Ref × Input) Response (Response × Response) :=
  .query (one, input) (fun first => .query (two, input) (fun second => .done (first, second)))

omit [DecidableEq Input] [Fintype Response] [Nonempty Response] in
theorem readPair_bound (one two : Ref) (input : Input) : (readPair (Response := Response) one two input).BoundedQueries 2 :=
  .query _ _ _ (fun _ => .query _ _ _ (fun _ => .done _ _))

theorem readPair_run (one two : Ref) (input : Input) :
    (readPair (Response := Response) one two input).run (service RandomOracle.oracle) [] =
      (uniform Response).map (fun value =>
        (⟨(value, value), [(input, value)], [((one, input), value), ((two, input), value)]⟩ :
          Outcome (Ref × Input) Response (Response × Response) (RandomOracle.Table Input Response))) := by
  simp [readPair, Program.run, service, RandomOracle.oracle, PMF.bind_map, PMF.pure_map, Function.comp_def]
  rfl

theorem readPair_results (one two : Ref) (input : Input) :
    ((readPair (Response := Response) one two input).run (service RandomOracle.oracle) []).map Outcome.result =
      Copyability.shared (uniform Response) := by
  rw [readPair_run, PMF.map_comp]
  rfl

/-- A deliberately reset pair of servers: the second read starts from [],
not from the first read's updated table. -/
noncomputable def resetReads (input : Input) : PMF (Response × Response) :=
  (RandomOracle.oracle ([] : RandomOracle.Table Input Response) input).bind (fun first =>
    (RandomOracle.oracle ([] : RandomOracle.Table Input Response) input).map (fun second => (first.2, second.2)))

theorem resetReads_results (input : Input) : resetReads (Response := Response) input =
    Copyability.independent (uniform Response) (uniform Response) := by
  simp only [resetReads, RandomOracle.oracle, List.lookup_nil, PMF.bind_map, PMF.map_comp, Function.comp_def]
  rfl

omit [Fintype Response] [Nonempty Response] in
theorem shared_not_reset (one two : Ref) (input : Input) :
    ((readPair (Response := Bool) one two input).run (service RandomOracle.oracle) []).map Outcome.result ≠
      resetReads (Response := Bool) input := by
  rw [readPair_results, resetReads_results]
  exact Copyability.fair_not_copyable

end CryptoOracle.SharedReference
