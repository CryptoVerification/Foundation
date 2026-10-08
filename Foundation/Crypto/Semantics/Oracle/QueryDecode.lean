import Foundation.Crypto.Semantics.Oracle.QueryMap

/-! Decode a faithfully encoded query interface while retaining the complete
joint result, state and transcript. This is semantic observation, not a CPU
certificate for arbitrary host-language encoding or decoding functions. -/
namespace CryptoOracle.Program
open Foundation.Probability
universe u v w x y s
set_option backward.isDefEq.respectTransparency false

theorem mapQueries_run_decoded {Request : Type u} {Response : Type v} {Result : Type w}
    {TargetRequest : Type x} {TargetResponse : Type y} {State : Type s}
    (request : Request → TargetRequest) (response : TargetResponse → Response)
    (decode : Response → TargetResponse) (hDecode : ∀ value, decode (response value) = value)
    (p : Program Request Response Result) (oracle : Oracle TargetRequest TargetResponse State) (state : State) :
    (p.mapQueries request response).run oracle state =
      (p.run (adaptOracle request response oracle) state).map (mapTranscript request decode) := by
  have h := congrArg (fun distribution => distribution.map (mapTranscript id decode))
    (mapQueries_run request response p oracle state)
  rw [PMF.map_comp, PMF.map_comp] at h
  have hl : (mapTranscript id decode ∘ mapTranscript id response :
      Outcome TargetRequest TargetResponse Result State → Outcome TargetRequest TargetResponse Result State) = id := by
    funext out
    cases out
    simp [mapTranscript, Function.comp_def, List.map_map, hDecode]
  have hr : (mapTranscript id decode ∘ mapTranscript request id :
      Outcome Request Response Result State → Outcome TargetRequest TargetResponse Result State) =
        mapTranscript request decode := by
    funext out
    cases out
    simp [mapTranscript, Function.comp_def, List.map_map]
  rw [hl, hr, PMF.map_id] at h
  exact h

end CryptoOracle.Program
