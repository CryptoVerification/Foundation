import Foundation.Crypto.Semantics.ExecutionStage
import Foundation.Crypto.Semantics.Procedure

/-! Bridge procedure contracts and source-indexed execution refinements.
A source coordinate may include layout invariants. Its embedding must match
both physical entry and physical return; neither direction compiles that
proof coordinate into a new runtime program. Actual joint costs are retained. -/
namespace Foundation.Probability.TimedExecution.Stage
universe u v
variable {Source : Type u} {Target : Type v}
    {step : Target → PMF Target} {embed : Source → Target}

noncomputable def ofProcedure (P : Procedure step Source Source)
    (hEntry : ∀ source, P.entry source = embed source)
    (hExit : ∀ source next, P.exit source next = embed next)
    (start : Source) : Stage step embed start where
  budget := P.budget start
  outcome := P.costed start
  bounded := P.bounded start
  law := by
    intro horizon hBudget
    simpa only [hEntry, hExit] using P.law start horizon hBudget

/-- Package state-dependent stages as a composable procedure. No extra
transition or padding is inserted by the conversion. -/
noncomputable def procedure (next : ∀ source, Stage step embed source) :
    Procedure step Source Source where
  entry := embed
  exit := fun _ => embed
  semantics := fun source => (next source).outcome.map Prod.fst
  costed := fun source => (next source).outcome
  budget := fun source => (next source).budget
  bounded := fun source => (next source).bounded
  correct := fun _ => rfl
  law := fun source => (next source).law

/-- Finite adaptive composition can be passed directly to the existing
procedure rules. The budget is uniform; durations remain branch dependent. -/
noncomputable def iteratedProcedure (next : ∀ source, Stage step embed source)
    (cap : Nat) (hCap : ∀ source, (next source).budget ≤ cap) (count : Nat) :
    Procedure step Source Source :=
  procedure (iterate next cap hCap count)

theorem iteratedProcedure_budget (next : ∀ source, Stage step embed source)
    (cap : Nat) (hCap : ∀ source, (next source).budget ≤ cap) (count : Nat) (start : Source) :
    (iteratedProcedure next cap hCap count).budget start = count * cap :=
  iterate_budget next cap hCap count start

theorem iteratedProcedure_semantics (next : ∀ source, Stage step embed source)
    (cap : Nat) (hCap : ∀ source, (next source).budget ≤ cap)
    (sourceStep : Source → PMF Source)
    (hStep : ∀ source, (next source).outcome.map Prod.fst = sourceStep source)
    (count : Nat) (start : Source) :
    (iteratedProcedure next cap hCap count).semantics start = eval sourceStep count start :=
  iterate_distribution next cap hCap sourceStep hStep count start

/-- Construct the iterated contract from existing procedures with checked
physical handoffs. Source invariants belong in the input/output type. -/
noncomputable def iterateProcedure (P : Procedure step Source Source)
    (hEntry : ∀ source, P.entry source = embed source)
    (hExit : ∀ source next, P.exit source next = embed next)
    (cap : Nat) (hCap : ∀ source, P.budget source ≤ cap) (count : Nat) :
    Procedure step Source Source :=
  iteratedProcedure (ofProcedure P hEntry hExit) cap hCap count

theorem iterateProcedure_semantics (P : Procedure step Source Source)
    (hEntry : ∀ source, P.entry source = embed source)
    (hExit : ∀ source next, P.exit source next = embed next)
    (cap : Nat) (hCap : ∀ source, P.budget source ≤ cap) (count : Nat) (start : Source) :
    (iterateProcedure P hEntry hExit cap hCap count).semantics start = eval P.semantics count start :=
  iteratedProcedure_semantics (ofProcedure P hEntry hExit) cap hCap P.semantics P.correct count start

/-- Completion still requires an absorbing physical exit at every supported
logical result. A finite iteration alone is not a stopping certificate. -/
theorem iterateProcedure_final (P : Procedure step Source Source)
    (hEntry : ∀ source, P.entry source = embed source)
    (hExit : ∀ source next, P.exit source next = embed next)
    (cap : Nat) (hCap : ∀ source, P.budget source ≤ cap) (count : Nat) (start : Source)
    (hFinal : ∀ final ∈ (eval P.semantics count start).support,
      step (embed final) = PMF.pure (embed final))
    (horizon : Nat) (hBudget : count * cap ≤ horizon) :
    eval step horizon (embed start) = (eval P.semantics count start).map embed :=
  iterate_final_law (ofProcedure P hEntry hExit) cap hCap P.semantics P.correct
    count start hFinal horizon hBudget

end Foundation.Probability.TimedExecution.Stage

namespace Foundation.Probability.TimedExecution.Procedure
universe u v w
variable {State : Type u} {Input : Type v} {Output : Type w} {step : State → PMF State}

/-- A physical-output stage permits composition with invariant-indexed stages
without changing or discarding any physical exit data or actual duration. -/
noncomputable def toStage (P : Procedure step Input Output) (input : Input) :
    Stage step id (P.entry input) where
  budget := P.budget input
  outcome := (P.toBlock input).outcome
  bounded := (P.toBlock input).bounded
  law := (P.toBlock input).law

theorem toStage_distribution (P : Procedure step Input Output) (input : Input) :
    (P.toStage input).outcome.map Prod.fst = (P.semantics input).map (P.exit input) := by
  have h := congrArg (fun distribution => distribution.map (P.exit input)) (P.correct input)
  simpa only [toStage, toBlock, PMF.map_comp, Function.comp_def] using h

end Foundation.Probability.TimedExecution.Procedure
