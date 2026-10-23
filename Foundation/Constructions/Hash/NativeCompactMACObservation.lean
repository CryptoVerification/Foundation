import Foundation.Constructions.Hash.NativeCompactMACQueryLaw
import Foundation.Constructions.Hash.NativeCompactMACExecutionCorrectness

/-! The complete physical MAC execution refines an independently stated
four-query lazy-oracle reference law. The projection retains the actual
final caller, cache and ordered transcript; the private cache is never reset. -/
namespace Foundation.Hash.Native.CompactMACExecution
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
open CompactMACRound
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

abbrev Table := PolygraphOracle.Table 8 0
abbrev Observed (Source : Type) := Table × Configuration Source

def project {State Source : Type} (output : Output State Source) : Observed Source := (output.1.table, output.2)

noncomputable def decodedOracle (table : Table) (message : Message) : PMF (Table × Tag) :=
  (RandomOracle.oracle table (Backend.key message)).map (fun answer => (answer.1, decodeTag answer.2.toList))

variable {State Source Result : Type}

theorem bind_projection (distribution : PMF (Retained State × Tag)) (reference : PMF (Table × Tag))
    (law : distribution.map (fun answer => (answer.1.table, answer.2)) = reference)
    (next : Table × Tag → PMF Result) :
    distribution.bind (fun answer => next (answer.1.table, answer.2)) = reference.bind next := by
  rw [← law, PMF.bind_map]
  rfl

variable (oracle : BitOracle State) (callerOracle : BitOracle Source)
    (ret : Retained State) (callerState : Source) (trace : List (List Bool × List Bool))

theorem firstQuery_law (coin : Bool) :
    ((firstQuery oracle callerOracle ret callerState trace coin).semantics ()).map
      (fun answer => (answer.1.table, answer.2)) = decodedOracle ret.table (firstMessage coin) := by
  unfold firstQuery
  rw [prefixed_semantics]
  apply query_law

theorem secondQuery_law (coin : Bool) (first : Tag) :
    ((secondQuery oracle callerOracle ret callerState trace coin first).semantics ()).map
      (fun answer => (answer.1.table, answer.2)) = decodedOracle ret.table (secondMessage first) := by
  unfold secondQuery
  rw [prefixed_semantics]
  apply query_law

theorem repeatedQuery_law (coin : Bool) (second : Tag) :
    ((repeatedQuery oracle callerOracle ret callerState trace coin second).semantics ()).map
      (fun answer => (answer.1.table, answer.2)) = decodedOracle ret.table (firstMessage coin) := by
  unfold repeatedQuery
  rw [prefixed_semantics]
  apply query_law

theorem verifyQuery_law (coin : Bool) (second repeated : Tag) :
    ((verifyQuery oracle callerOracle ret callerState trace coin second repeated).semantics ()).map
      (fun answer => (answer.1.table, answer.2)) = decodedOracle ret.table 7 := by
  unfold verifyQuery
  rw [prefixed_semantics]
  apply query_law

noncomputable def finalReference (table : Table) (callerState : Source)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate actual : Tag) : Observed Source :=
  (table, ⟨callerState, .running (Native.comparisonResult coin candidate actual).1, trace⟩)

noncomputable def lastReference (table : Table) (callerState : Source)
    (trace : List (List Bool × List Bool)) (coin : Bool) (second repeated : Tag) : PMF (Observed Source) :=
  (decodedOracle table 7).map (fun actual =>
    finalReference actual.1 callerState (Native.extendTrace 7 actual.2 trace)
      coin (if coin then repeated else second) actual.2)

noncomputable def repeatReference (table : Table) (callerState : Source)
    (trace : List (List Bool × List Bool)) (coin : Bool) (second : Tag) : PMF (Observed Source) :=
  (decodedOracle table (firstMessage coin)).bind (fun repeated =>
    lastReference repeated.1 callerState (Native.extendTrace (firstMessage coin) repeated.2 trace) coin second repeated.2)

noncomputable def secondReference (table : Table) (callerState : Source)
    (trace : List (List Bool × List Bool)) (coin : Bool) (first : Tag) : PMF (Observed Source) :=
  (decodedOracle table (secondMessage first)).bind (fun second =>
    repeatReference second.1 callerState (Native.extendTrace (secondMessage first) second.2 trace) coin second.2)

noncomputable def firstReference (table : Table) (callerState : Source)
    (trace : List (List Bool × List Bool)) (coin : Bool) : PMF (Observed Source) :=
  (decodedOracle table (firstMessage coin)).bind (fun first =>
    secondReference first.1 callerState (Native.extendTrace (firstMessage coin) first.2 trace) coin first.2)

noncomputable def reference (table : Table) (callerState : Source)
    (trace : List (List Bool × List Bool)) : PMF (Observed Source) :=
  sampleBit.bind (firstReference table callerState trace)

theorem finish_projection (coin : Bool) (candidate actual : Tag) :
    ((finish oracle callerOracle ret callerState trace coin candidate actual).semantics ()).map project =
      PMF.pure (finalReference ret.table callerState trace coin candidate actual) := by
  simp only [finish, Procedure.observe, nativeSegment, TimedExecution.Procedure.ofFixed, PMF.pure_map]
  rfl

theorem last_projection (coin : Bool) (second repeated : Tag) :
    ((last oracle callerOracle ret callerState trace coin second repeated).semantics ()).map project =
      lastReference ret.table callerState trace coin second repeated := by
  unfold last
  rw [follow_semantics, PMF.map_bind]
  simp_rw [finish_projection]
  exact bind_projection _ _ (verifyQuery_law oracle callerOracle ret callerState trace coin second repeated)
    (fun actual => PMF.pure (finalReference actual.1 callerState (Native.extendTrace 7 actual.2 trace)
      coin (if coin then repeated else second) actual.2))

theorem repeat_projection (coin : Bool) (second : Tag) :
    ((repeatedStage oracle callerOracle ret callerState trace coin second).semantics ()).map project =
      repeatReference ret.table callerState trace coin second := by
  unfold repeatedStage
  rw [follow_semantics, PMF.map_bind]
  simp_rw [last_projection]
  exact bind_projection _ _ (repeatedQuery_law oracle callerOracle ret callerState trace coin second)
    (fun repeated => lastReference repeated.1 callerState
      (Native.extendTrace (firstMessage coin) repeated.2 trace) coin second repeated.2)

theorem second_projection (coin : Bool) (first : Tag) :
    ((second oracle callerOracle ret callerState trace coin first).semantics ()).map project =
      secondReference ret.table callerState trace coin first := by
  unfold second
  rw [follow_semantics, PMF.map_bind]
  simp_rw [repeat_projection]
  exact bind_projection _ _ (secondQuery_law oracle callerOracle ret callerState trace coin first)
    (fun second => repeatReference second.1 callerState
      (Native.extendTrace (secondMessage first) second.2 trace) coin second.2)

theorem first_projection (coin : Bool) :
    ((first oracle callerOracle ret callerState trace coin).semantics ()).map project =
      firstReference ret.table callerState trace coin := by
  unfold first
  rw [follow_semantics, PMF.map_bind]
  simp_rw [second_projection]
  exact bind_projection _ _ (firstQuery_law oracle callerOracle ret callerState trace coin)
    (fun first => secondReference first.1 callerState
      (Native.extendTrace (firstMessage coin) first.2 trace) coin first.2)

theorem whole_projection :
    ((whole oracle callerOracle ret callerState trace).semantics ()).map project =
      reference ret.table callerState trace := by
  unfold whole
  rw [follow_semantics, PMF.map_bind]
  simp_rw [first_projection]
  rfl

/-- Only actual cells of the retained server and the actual complete caller
are observed here. No logical table certificate is read at runtime. -/
def runtimeObservation (control : CompactMACRound.Control State Source) : Option (List Bool × Configuration Source) :=
  match control with
  | .source saved caller => match saved.control with
      | .running machine => some (machine.inputTape.bits, caller)
      | _ => none
  | _ => none

def render (observation : Observed Source) : Option (List Bool × Configuration Source) :=
  some (SimulatorLookup.tableBits observation.1, observation.2)

theorem runtimeObservation_embed (output : Output State Source) : runtimeObservation (embed output) = render (project output) := by
  simp only [runtimeObservation, embed, output.1.hControl, render, project, output.1.tableLayout.bits,
    Tape.bits_ofBits]

/-- Whole physical execution has the reference distribution jointly for
final private table cells, complete caller state, and every recorded call. -/
theorem runtime_law (horizon : Nat) (enough : 584 * ret.table.length + 2091 ≤ horizon) :
    (TimedExecution.eval (CompactMACRound.step oracle callerOracle) horizon
      (.source ret.saved ⟨callerState, .running {}, trace⟩)).map runtimeObservation =
      (reference ret.table callerState trace).map render := by
  rw [whole_run oracle callerOracle ret callerState trace horizon enough, PMF.map_comp]
  have same : (runtimeObservation ∘ embed : Output State Source → Option (List Bool × Configuration Source)) = render ∘ project :=
    funext runtimeObservation_embed
  rw [same, ← PMF.map_comp, whole_projection]

end Foundation.Hash.Native.CompactMACExecution
