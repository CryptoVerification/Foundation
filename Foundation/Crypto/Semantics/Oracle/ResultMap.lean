import Foundation.Crypto.Semantics.Oracle.Program

/-! Result decoding for oracle programs preserves state and the complete
query transcript. This does not change queries. No execution-time guarantee
for an arbitrary decoding function is inferred from this semantic operation. -/
namespace CryptoOracle.Program
open Foundation.Probability
universe u v w z s
set_option backward.isDefEq.respectTransparency false

variable {Request : Type u} {Response : Type v} {Result : Type w} {Decoded : Type z}

def mapResult (decode : Result → Decoded) : Program Request Response Result → Program Request Response Decoded
  | .done result => .done (decode result)
  | .query request next => .query request (fun response => mapResult decode (next response))
  | .coin next => .coin (fun bit => mapResult decode (next bit))

def decodeOutcome {State : Type s} (decode : Result → Decoded)
    (out : Outcome Request Response Result State) : Outcome Request Response Decoded State :=
  ⟨decode out.result, out.state, out.trace⟩

/-- Decoding the final result preserves the joint state/transcript law. -/
theorem mapResult_run {State : Type s} (decode : Result → Decoded)
    (p : Program Request Response Result) (oracle : Oracle Request Response State) (state : State) :
    (p.mapResult decode).run oracle state = (p.run oracle state).map (decodeOutcome decode) := by
  induction p generalizing state with
  | done result => simp [mapResult, run, decodeOutcome, PMF.pure_map]
  | query request next ih =>
      simp only [mapResult, run, PMF.map_bind]
      congr 1
      funext response
      rw [ih, PMF.map_comp, PMF.map_comp]
      rfl
  | coin next ih =>
      simp only [mapResult, run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit state

theorem mapResult_queries (decode : Result → Decoded) {p : Program Request Response Result} {q : Nat}
    (h : p.BoundedQueries q) : (p.mapResult decode).BoundedQueries q := by
  induction h with
  | done result q => exact .done _ _
  | query request next q h ih => exact .query _ _ q ih
  | coin next q h ih => exact .coin _ q ih

end CryptoOracle.Program
