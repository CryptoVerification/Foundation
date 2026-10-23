import Foundation.Crypto.Semantics.Oracle.RandomOracleRepresentation
import Foundation.Examples.RandomFunctionMACRepairGame

/-! Genuinely different lazy-cache games, with Fin 256 public responses and
8-bit stored responses. A history-dependent representation is selected after
signing, then an operational decoded-cache oracle performs verification. -/
namespace Foundation.Symmetric.RandomFunctionMACRepresentationGame
open Foundation.Probability Foundation.Probability.SelectedCouplingGraph
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACPosterior RandomFunctionMACCouplingRepair
open RandomFunctionMACRepairGame
set_option backward.isDefEq.respectTransparency false

abbrev StoredOutcome := Outcome (Fin 8) (Fin 256) Bool (Table (Fin 8) (Bits 8))

def codec (mask : Bool) (input : Fin 8) : Fin 256 ≃ Bits 8 :=
  RandomFunctionMACNativeCaller.Backend.tagEquiv.trans (twistEquiv 8 (if input = 7 then mask else false))

def encode (mask : Bool) : GameOutcome → StoredOutcome := Program.mapState (Representation.table (codec mask))

def decode (mask : Bool) : StoredOutcome → GameOutcome :=
  Program.mapState (Representation.table (fun input => (codec mask input).symm))

theorem decode_encode (mask : Bool) (out : GameOutcome) : decode mask (encode mask out) = out := by
  cases out
  simp only [decode, encode, Program.mapState, Representation.table_inverse]

def lastProgram (past : SigningOutcome) : Program (Fin 8) (Fin 256) Bool :=
  .query 7 fun response => .done (decide (response = past.result.2))

noncomputable def suffix (mask : Bool) (past : SigningOutcome) : PMF StoredOutcome :=
  ((lastProgram past).run (Representation.oracle (codec mask)) (Representation.table (codec mask) past.state)).map
    (fun out => {out with trace := past.trace ++ out.trace})

noncomputable def storedGame (masks : SigningOutcome → Bool) : PMF (SigningOutcome × StoredOutcome) :=
  signingHistory.bind fun past => (suffix (masks past) past).map fun out => (past, out)

theorem suffix_law (mask : Bool) (past : SigningOutcome) (supported : past ∈ signingHistory.support) :
    suffix mask past = (uniform (Bits 8)).map (fun tag => encode mask (finish past tag)) := by
  unfold suffix
  rw [← Representation.run]
  rw [lastProgram, Program.run, fresh past.state 7 (signing_fresh past supported)]
  simp only [PMF.bind_map, Program.run, PMF.pure_map, PMF.map_comp, Function.comp_def]
  have law := congrArg (fun p => p.map (fun tag => encode mask (finishTag past tag)))
    RandomFunctionMACNativeCaller.Backend.uniform_decoded
  symm
  simpa only [finish, finishTag, encode, Program.mapState, PMF.map, PMF.bind_bind,
    PMF.pure_bind, Function.comp_def] using law

def storedAnswer (out : StoredOutcome) : Bits 8 :=
  (out.state.lookup 7).getD (fun _ => false)

theorem stored_answer_encode_finish (mask : Bool) (past : SigningOutcome) (tag : Bits 8) :
    storedAnswer (encode mask (finish past tag)) = twist mask tag := by
  change codec mask 7 (RandomFunctionMACNativeCaller.decodeTag tag.toList) = twist mask tag
  change twist mask (RandomFunctionMACNativeCaller.Backend.tagBits
    (RandomFunctionMACNativeCaller.decodeTag tag.toList)) = twist mask tag
  rw [RandomFunctionMACNativeCaller.Backend.tagBits_decode]

theorem untwisted (tag : Bits 8) : twist false tag = tag := by
  funext index
  simp only [twist]
  cases tag index <;> rfl

variable {Vertex Edge : Type} (G : Graph Vertex Edge)

noncomputable def joint (potential : SigningOutcome → Vertex → Bool) :
    PMF (RetainedHistory × (Vertex → StoredOutcome)) :=
  (games (fun (_ : SigningOutcome) (_ : Vertex) => false)).map fun pair =>
    (pair.1, fun vertex => encode (potential pair.1.1 vertex) (pair.2 vertex))

include G in
/-- Every vertex marginal is its operational represented-cache game. -/
theorem joint_vertex (potential : SigningOutcome → Vertex → Bool) (vertex : Vertex) :
    (joint potential).map (fun pair => (pair.1.1, pair.2 vertex)) =
      storedGame (fun past => potential past vertex) := by
  have vertexLaw := context_joint_vertex G 8 signingHistory (fun _ _ => false) vertex
  rw [← actual_joint_projection G (fun _ _ => false), PMF.map_comp] at vertexLaw
  have law := congrArg (fun p => p.map (fun pair =>
    (pair.1, encode (potential pair.1 vertex) (finish pair.1 pair.2)))) vertexLaw
  simp only [joint, games, PMF.map_comp, PMF.map_bind, Function.comp_def] at law ⊢
  rw [law]
  apply bind_congr_of_support
  intro past supported
  rw [suffix_law _ past supported, PMF.map_comp]
  rfl

include G in
/-- Decoding preserves the entire original final game output. -/
theorem decoded_vertex (potential : SigningOutcome → Vertex → Bool) (vertex : Vertex) :
    (joint potential).map (fun pair => decode (potential pair.1.1 vertex) (pair.2 vertex)) =
      RandomFunctionMACNativeCaller.target.run RandomOracle.oracle [] := by
  simpa only [joint, PMF.map_comp, Function.comp_def, decode_encode] using
    vertex_game_law G (fun _ _ => false) vertex

/-- The stored values themselves determine the correspondence diagram.
The public verification answer is shared; only its stored encoding differs. -/
theorem joint_stored_answers (potential : SigningOutcome → Vertex → Bool) :
    (joint potential).map (fun pair =>
      (pair.1.1, fun vertex => storedAnswer (pair.2 vertex))) =
      contextJoint G 8 signingHistory potential := by
  have law := congrArg (fun p => p.map (fun pair : SigningOutcome × Bits 8 =>
    (pair.1, fun vertex => twist (potential pair.1 vertex) pair.2))) actual_answer_law
  simpa only [joint, games, actualJoint, PMF.map_comp, PMF.map_bind, Function.comp_def,
    stored_answer_encode_finish, untwisted, contextJoint, tagJoint] using law

/-- Edge labels are extracted from the operational cache representation,
not assigned to several copies of an identical stored game. -/
theorem derived_edge_law (potential : SigningOutcome → Vertex → Bool) (edge : Edge) :
    (joint potential).map (fun pair => (pair.1.1,
      (storedAnswer (pair.2 (G.source edge)), storedAnswer (pair.2 (G.target edge))))) =
      contextEdge 8 signingHistory (fun past => G.boundary (potential past)) edge := by
  have law := context_joint_edge G 8 signingHistory potential
    (fun past => G.boundary (potential past)) (fun _ _ => rfl) edge
  rw [← joint_stored_answers G potential, PMF.map_comp] at law
  exact law

/-- The representation change really changes stored values. Both public
responses remain zero because the oracle decodes before returning them. -/
theorem distinct_storage :
    (Representation.table (codec false) [(7, (0 : Fin 256))]).lookup 7 ≠
      (Representation.table (codec true) [(7, (0 : Fin 256))]).lookup 7 := by
  decide_cbv

def publicAnswer (out : StoredOutcome) : Fin 256 :=
  ((out.trace.reverse.head?).map Prod.snd).getD 0

theorem public_answer_encode_finish (mask : Bool) (past : SigningOutcome) (tag : Bits 8) :
    RandomFunctionMACNativeCaller.Backend.tagBits (publicAnswer (encode mask (finish past tag))) = tag := by
  simp only [publicAnswer, encode, finish, finishTag, Program.mapState, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.head?_cons, Option.map_some, Option.getD_some]
  exact RandomFunctionMACNativeCaller.Backend.tagBits_decode tag

theorem stored_game_relation (masks : SigningOutcome → Bool) (pair : SigningOutcome × StoredOutcome)
    (supported : pair ∈ (storedGame masks).support) :
    storedAnswer pair.2 = twist (masks pair.1)
      (RandomFunctionMACNativeCaller.Backend.tagBits (publicAnswer pair.2)) := by
  rw [storedGame, PMF.mem_support_bind_iff] at supported
  obtain ⟨past, reachable, supported⟩ := supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨out, selected, rfl⟩ := supported
  rw [suffix_law _ past reachable, PMF.mem_support_map_iff] at selected
  obtain ⟨tag, _, rfl⟩ := selected
  rw [stored_answer_encode_finish, public_answer_encode_finish]

/-- The actual joint output laws differ: the cache-to-public-response
correlation exposes the representation, although decoding gives one game. -/
theorem stored_games_distinct : storedGame (fun _ => false) ≠ storedGame (fun _ => true) := by
  intro same
  obtain ⟨pair, supported⟩ := (storedGame (fun _ => false)).support_nonempty
  have plain := stored_game_relation (fun _ => false) pair supported
  rw [same] at supported
  have masked := stored_game_relation (fun _ => true) pair supported
  rw [untwisted] at plain
  have fixed := masked.symm.trans plain
  have bit := congrFun fixed 0
  simp only [twist] at bit
  cases value : RandomFunctionMACNativeCaller.Backend.tagBits (publicAnswer pair.2) 0 <;>
    simp [value] at bit

end Foundation.Symmetric.RandomFunctionMACRepresentationGame
