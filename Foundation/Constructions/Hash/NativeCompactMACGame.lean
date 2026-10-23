import Foundation.Constructions.Hash.NativeCompactMACTypedOracle

/-! Connect the full native backend execution to the original typed MAC
game, preserving its final cache cells, verification result and transcript. -/
namespace Foundation.Hash.Native.CompactMACExecution
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
open CompactMACRound
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

variable {State Source : Type}

def relocate (callerState : Source) (frame : Configuration Table) : Observed Source :=
  (frame.state, ⟨callerState, frame.control, frame.reverseTrace⟩)

theorem reference_executionLaw (table : Table) (callerState : Source)
    (trace : List (List Bool × List Bool)) :
    reference table callerState trace =
      (sampleBit.bind (Native.executionLaw decodedOracle table trace)).map (relocate callerState) := by
  unfold reference firstReference secondReference repeatReference lastReference finalReference Native.executionLaw
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

def gameObservation (output : Observed Source) : Outcome Message Tag Bool Table :=
  ⟨Native.verdict output.2.control, output.1,
    output.2.reverseTrace.reverse.map (fun entry => (decodeMessage entry.1, decodeTag entry.2))⟩

theorem reference_game (table : Table) (callerState : Source) :
    (reference table callerState []).map gameObservation = target.run decodedOracle table := by
  rw [reference_executionLaw, PMF.map_comp]
  have original := Native.observation_law decodedOracle table
  rw [Native.whole_run] at original
  exact original

theorem reference_typed_game (table : TypedTable) (callerState : Source) :
    (reference (encodeTable table) callerState []).map gameObservation =
      (target.run RandomOracle.oracle table).map (Program.mapState encodeTable) := by
  rw [reference_game]
  exact (decodedOracle_run target table).symm

/-- Physical cells, verification bit, and every decoded request/response.
This observation reads an existing final frame; it is not a machine opcode. -/
def gameView (control : CompactMACRound.Control State Source) :
    Option (List Bool × Bool × List (Message × Tag)) :=
  (runtimeObservation control).map fun output =>
    (output.1, Native.verdict output.2.control,
      output.2.reverseTrace.reverse.map (fun entry => (decodeMessage entry.1, decodeTag entry.2)))

def renderGame (output : Outcome Message Tag Bool Table) : Option (List Bool × Bool × List (Message × Tag)) :=
  some (SimulatorLookup.tableBits output.state, output.result, output.trace)

variable (oracle : BitOracle State) (callerOracle : BitOracle Source)
    (ret : Retained State) (callerState : Source)

theorem runtime_game_law (table : TypedTable) (encoding : ret.table = encodeTable table)
    (horizon : Nat) (enough : 584 * ret.table.length + 2091 ≤ horizon) :
    (TimedExecution.eval (CompactMACRound.step oracle callerOracle) horizon
      (.source ret.saved ⟨callerState, .running {}, []⟩)).map gameView =
      (target.run RandomOracle.oracle table).map (renderGame ∘ Program.mapState encodeTable) := by
  have law := congrArg (PMF.map (Option.map (fun output : List Bool × Configuration Source =>
    (output.1, Native.verdict output.2.control,
      output.2.reverseTrace.reverse.map (fun entry => (decodeMessage entry.1, decodeTag entry.2))))))
    (runtime_law oracle callerOracle ret callerState [] horizon enough)
  simp only [PMF.map_comp] at law
  change _ = (reference ret.table callerState []).map (renderGame ∘ gameObservation) at law
  rw [encoding] at law
  have coded := congrArg (PMF.map renderGame) (reference_typed_game table callerState)
  simp only [PMF.map_comp] at coded
  exact law.trans coded

def physicalVerdict (control : CompactMACRound.Control State Source) : Bool :=
  match control with
  | .source _ frame => Native.verdict frame.control
  | _ => false

theorem runtime_verdict_law (table : TypedTable) (encoding : ret.table = encodeTable table)
    (horizon : Nat) (enough : 584 * ret.table.length + 2091 ≤ horizon) :
    (TimedExecution.eval (CompactMACRound.step oracle callerOracle) horizon
      (.source ret.saved ⟨callerState, .running {}, []⟩)).map physicalVerdict =
      (target.run RandomOracle.oracle table).map Outcome.result := by
  rw [whole_run oracle callerOracle ret callerState [] horizon enough, PMF.map_comp]
  change ((whole oracle callerOracle ret callerState []).semantics ()).map
    ((fun output : Observed Source => Native.verdict output.2.control) ∘ project) = _
  rw [← PMF.map_comp, whole_projection, encoding]
  have observed := congrArg (PMF.map Outcome.result) (reference_typed_game table callerState)
  simpa only [PMF.map_comp, gameObservation, Program.mapState, Function.comp_def] using observed

end Foundation.Hash.Native.CompactMACExecution
