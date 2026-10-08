import Foundation.Crypto.Semantics.ProcedureIteration

/-! Reusable contract constructors for fixed continuations and indexed
families over one actual transition system. No transition, loading or
resetting is introduced by these proof-level constructors. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
variable {State : Type u} {Input : Type v} {Middle : Type w} {Output : Type x}
    {step : State → PMF State}
set_option backward.isDefEq.respectTransparency false

/-- Execute a fixed continuation only when its actual entry equals every
supported physical exit of the first procedure. The first logical result
can then be forgotten without forgetting its actual time or state effects. -/
noncomputable def andThen (P : Procedure step Input Middle) (Q : Procedure step Unit Output)
    (handoff : ∀ input middle, middle ∈ (P.semantics input).support → Q.entry () = P.exit input middle) :
    Procedure step Input Output :=
  (P.seq (Q.reindex (fun _ : Middle => ())) handoff (fun _ => Q.budget ()) (fun _ _ _ => Nat.le_refl _)).observe
    Prod.snd (fun _ output => Q.exit () output) (fun _ _ _ => rfl)

theorem andThen_entry (P : Procedure step Input Middle) (Q : Procedure step Unit Output) (handoff) (input : Input) :
    (P.andThen Q handoff).entry input = P.entry input := rfl

theorem andThen_exit (P : Procedure step Input Middle) (Q : Procedure step Unit Output) (handoff)
    (input : Input) (output : Output) : (P.andThen Q handoff).exit input output = Q.exit () output := rfl

theorem andThen_budget (P : Procedure step Input Middle) (Q : Procedure step Unit Output) (handoff) (input : Input) :
    (P.andThen Q handoff).budget input = P.budget input + Q.budget () := rfl

theorem andThen_semantics (P : Procedure step Input Middle) (Q : Procedure step Unit Output) (handoff) (input : Input) :
    (P.andThen Q handoff).semantics input = Q.semantics () := by
  change ((P.semantics input).bind (fun middle => (Q.semantics ()).map (fun output => (middle, output)))).map Prod.snd = _
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.map_id]
  change ((P.semantics input).bind (fun _ => (Q.semantics ()).map id)) = _
  rw [PMF.map_id]
  exact PMF.bind_const _ _

/-- The first result can be discarded, but its actual random cost is added
branch by branch to the continuation's actual random cost. -/
theorem andThen_costed (P : Procedure step Input Middle) (Q : Procedure step Unit Output) (handoff) (input : Input) :
    (P.andThen Q handoff).costed input = (P.costed input).bind (fun first =>
      (Q.costed ()).map (fun second => (second.1, first.2 + second.2))) := by
  simp only [andThen, observe, seq, reindex, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Index only the contracts; all members use the same physical step
relation. The caller must separately prepare the selected member's entry. -/
noncomputable def family {Index : Type v} (P : Index → Procedure step Unit Output) : Procedure step Index Output where
  entry := fun input => (P input).entry ()
  exit := fun input output => (P input).exit () output
  semantics := fun input => (P input).semantics ()
  costed := fun input => (P input).costed ()
  budget := fun input => (P input).budget ()
  bounded := fun input => (P input).bounded ()
  correct := fun input => (P input).correct ()
  law := fun input => (P input).law ()

theorem family_entry {Index : Type v} (P : Index → Procedure step Unit Output) (input : Index) :
    (family P).entry input = (P input).entry () := rfl

theorem family_budget {Index : Type v} (P : Index → Procedure step Unit Output) (input : Index) :
    (family P).budget input = (P input).budget () := rfl

theorem family_costed {Index : Type v} (P : Index → Procedure step Unit Output) (input : Index) :
    (family P).costed input = (P input).costed () := rfl

end Foundation.Probability.TimedExecution.Procedure
