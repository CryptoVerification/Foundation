import Foundation.Constructions.Hash.NativeConfiguredMACRound
import Foundation.Constructions.Hash.NativeCompactMACQueryLaw

/-! Distributional refinement of a retained physical compact-MAC query.
Reading a logical table and tag is a proof-side projection, never a runtime
reconstruction or an uncharged packet encoder. -/
namespace Foundation.Hash.Native.ConfiguredMACRound
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

open CompactMACRound

variable (callerCode : Code) {State Source : Type} (oracle : BitOracle State) (callerOracle : BitOracle Source)
    (ret : Retained State) (caller : Machine.Configuration) (callerState : Source)
    (trace : List (List Bool × List Bool)) (message : Message)
    (before after : List (Option Bool)) (active : caller.halted = false)
    (call : callerCode[caller.pc]? = some .call)
    (tape : caller.outputTape = RequestExport.packetTape before after (encodeMessage message))

theorem raw_tag_law :
    ((raw callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).map
      (fun output => frameTag output.2) =
      (RandomOracle.oracle ret.table (Backend.key message)).map (fun answer => decodeTag answer.2.toList) := by
  rw [raw_semantics]
  have law := CompactMACService.service_lazy oracle ret.saved.state ret.machine ret.saved.reverseTrace message ret.table ret.tableLayout
    callerCode callerOracle caller.advance callerState trace
  have observed := congrArg (PMF.map (fun result => frameTag result.2)) law
  simpa only [PMF.map_comp, Function.comp_def, frameTag_resumed] using observed

/-- Joint law includes the actual updated table, rather than just a tag
marginal. Physical frames remain in the original query's result and cost. -/
theorem query_law :
    ((query callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).map
      (fun answer => (answer.1.table, answer.2)) =
      (RandomOracle.oracle ret.table (Backend.key message)).map
        (fun answer => (answer.1, decodeTag answer.2.toList)) := by
  change (((certified callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).map
    (answer ret caller callerState trace message)).map (fun answer => (answer.1.table, answer.2)) = _
  rw [PMF.map_comp]
  have project : (fun output : {output // Returned ret caller callerState trace message output} =>
      ((answer ret caller callerState trace message output).1.table,
        (answer ret caller callerState trace message output).2)) =
      (fun output => (nextTable ret.table message (frameTag output.val.2), frameTag output.val.2)) :=
    funext (answer_projection ret caller callerState trace message)
  change ((certified callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).map
    (fun output => ((answer ret caller callerState trace message output).1.table,
      (answer ret caller callerState trace message output).2)) = _
  rw [project]
  change ((certified callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).map
    ((fun output => (nextTable ret.table message (frameTag output.2), frameTag output.2)) ∘ Subtype.val) = _
  rw [← PMF.map_comp]
  unfold certified
  rw [Procedure.certify_semantics]
  have tags := congrArg (PMF.map (fun tag => (nextTable ret.table message tag, tag)))
    (raw_tag_law callerCode oracle callerOracle ret caller callerState trace message before after active call tape)
  simp only [PMF.map_comp, Function.comp_def] at tags
  rw [tags]
  unfold PMF.map
  apply bind_congr_of_support
  intro result supported
  simp only [Function.comp_def]
  rw [PolygraphOracle.oracle_update ret.table (Backend.key message) result supported, update_as_if]
  simp only [nextTable, Backend.tagBits_decode]

end Foundation.Hash.Native.ConfiguredMACRound
