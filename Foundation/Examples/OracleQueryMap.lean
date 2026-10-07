import Foundation.Crypto.Semantics.Oracle.QueryReification

/-! An adaptive second query depends on the decoded first response. The
deterministic example checks final state, both responses, and query order. -/
namespace CryptoOracle.QueryMapExamples
open Foundation.Probability

def attack : Program Nat Bool Bool :=
  .query 0 (fun first => .query (if first then 0 else 1) .done)

noncomputable def oracle (state : Nat) (request : Bool) : PMF (Nat × Nat) :=
  PMF.pure (state + 1, if request then 7 else 2)

def request (value : Nat) : Bool := value % 2 == 1
def response (value : Nat) : Bool := value == 7

example : (attack.mapQueries request response).BoundedQueries 2 :=
  Program.mapQueries_queries request response
    (.query 0 _ 1 (fun _ => .query _ _ 0 (fun _ => .done _ 0)))

example : (attack.mapQueries request response).run oracle 100 =
    PMF.pure ⟨true, 102, [(false, 2), (true, 7)]⟩ := by
  simp [attack, Program.mapQueries, Program.run, oracle, request, response,
    PMF.pure_bind, PMF.pure_map]

-- Omitting the response decoder changes the second request and final result.
example : (attack.mapQueries request (fun _ => true)).run oracle 100 =
    PMF.pure ⟨true, 102, [(false, 2), (false, 2)]⟩ := by
  simp [attack, Program.mapQueries, Program.run, oracle, request,
    PMF.pure_bind, PMF.pure_map]

example : ((attack.mapQueries request response).run oracle 100).map
    (Program.mapTranscript id response) =
    PMF.pure ⟨true, 102, [(false, false), (true, true)]⟩ := by
  simp [attack, Program.mapQueries, Program.run, oracle, request, response,
    Program.mapTranscript, PMF.pure_bind, PMF.pure_map]

end CryptoOracle.QueryMapExamples
