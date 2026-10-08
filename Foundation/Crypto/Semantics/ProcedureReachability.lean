import Foundation.Crypto.Semantics.ProcedureInterval
import Foundation.Crypto.Semantics.ProcedurePhysical
import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.ProcedureInvariant
import Foundation.Crypto.Semantics.BoundaryReachability

/-! A residual execution law alone is not a proof that each reported return
was reached at its reported cost. Record that additional operational fact and
preserve it through ordinary contract constructors. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {Middle : Type w} {Output : Type x}
    {step : State → PMF State}

def Operational (P : Procedure step Input Output) : Prop :=
  ∀ input result, result ∈ (P.costed input).support →
    P.exit input result.1 ∈ (eval step result.2 (P.entry input)).support

theorem operational_ofFixed (entry : Input → State) (exit : Input → Output → State)
    (semantics : Input → PMF Output) (duration : Input → Nat)
    (run : ∀ input, eval step (duration input) (entry input) = (semantics input).map (exit input)) :
    Operational (Procedure.ofFixed step entry exit semantics duration run) := by
  intro input result hs
  change result ∈ ((semantics input).map (fun output => (output, duration input))).support at hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨output, ho, he⟩ := hs
  subst result
  change exit input output ∈ (eval step (duration input) (entry input)).support
  rw [run, PMF.mem_support_map_iff]
  exact ⟨output, ho, rfl⟩

theorem operational_reindex {NewInput : Type*} (P : Procedure step Input Output)
    (hP : Operational P) (view : NewInput → Input) : Operational (P.reindex view) :=
  fun input => hP (view input)

theorem operational_observe {Observed : Type*} (P : Procedure step Input Output)
    (hP : Operational P) (view : Output → Observed) (exit : Input → Observed → State)
    (hExit : ∀ input output, output ∈ (P.semantics input).support → exit input (view output) = P.exit input output) :
    Operational (P.observe view exit hExit) := by
  intro input result hs
  change result ∈ ((P.costed input).map (fun original => (view original.1, original.2))).support at hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨original, ho, he⟩ := hs
  subst result
  change exit input (view original.1) ∈ (eval step original.2 (P.entry input)).support
  rw [hExit input original.1 (P.result_support input original ho)]
  exact hP input original ho

theorem operational_physical (P : Procedure step Input Output) (hP : Operational P) :
    Operational P.physical := by
  intro input result hs
  rw [physical_costed, PMF.mem_support_map_iff] at hs
  obtain ⟨original, ho, he⟩ := hs
  subst result
  exact hP input original ho

theorem operational_dispatch (family : Input → Procedure step Unit Output)
    (hFamily : ∀ input, Operational (family input)) : Operational (dispatch family) :=
  fun input => hFamily input ()

theorem operational_certify (P : Procedure step Input Output) (hP : Operational P)
    (predicate : Output → Prop)
    (h : ∀ input output, output ∈ (P.semantics input).support → predicate output) :
    Operational (P.certify predicate h) := by
  intro input result hs
  have ho : (result.1.val, result.2) ∈ (P.costed input).support := by
    rw [← certify_costed P predicate h input, PMF.mem_support_map_iff]
    exact ⟨result, hs, rfl⟩
  exact hP input (result.1.val, result.2) ho

/-- Reachability is needed only at admissible inputs, just like invariant
closure and resource bounds. Certification preserves the actual cost. -/
theorem operational_restrictInvariant {Value : Type*} (P : Procedure step Value Value)
    (predicate : Value → Prop)
    (hClosed : ∀ input, predicate input → ∀ output ∈ (P.semantics input).support, predicate output)
    (hP : ∀ input, predicate input → ∀ result ∈ (P.costed input).support,
      P.exit input result.1 ∈ (eval step result.2 (P.entry input)).support) :
    Operational (P.restrictInvariant predicate hClosed) :=
  operational_certify (P.reindex Subtype.val) (fun input => hP input.val input.property) predicate _

set_option maxHeartbeats 1000000 in
theorem operational_seq (first : Procedure step Input Middle) (second : Procedure step Middle Output)
    (hFirst : Operational first) (hSecond : Operational second)
    (handoff : ∀ input middle, middle ∈ (first.semantics input).support → second.entry middle = first.exit input middle)
    (cap : Input → Nat)
    (hCap : ∀ input middle, middle ∈ (first.semantics input).support → second.budget middle ≤ cap input) :
    Operational (first.seq second handoff cap hCap) := by
  intro input result hs
  change result ∈ ((first.costed input).bind (fun middle => (second.costed middle.1).map
    (fun output => ((middle.1, output.1), middle.2 + output.2)))).support at hs
  rw [PMF.mem_support_bind_iff] at hs
  obtain ⟨middle, hm, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨output, ho, he⟩ := hs
  subst result
  change second.exit middle.1 output.1 ∈ (eval step (middle.2 + output.2) (first.entry input)).support
  rw [eval_add, PMF.mem_support_bind_iff]
  refine ⟨first.exit input middle.1, hFirst input middle hm, ?_⟩
  rw [← handoff input middle.1 (first.result_support input middle hm)]
  exact hSecond middle.1 output ho

theorem operational_interval {Source : Type*} (sourceStep : Source → PMF Source)
    (sourceBoundary : Source → Bool) (targetBoundary : State → Bool) (embed : Source → State)
    (hBoundary : ∀ source, targetBoundary (embed source) = sourceBoundary source)
    (hStep : ∀ source, sourceBoundary source = false → step (embed source) = (sourceStep source).map embed)
    (fuel : Nat) :
    Operational (interval sourceStep step sourceBoundary targetBoundary embed hBoundary hStep fuel) := by
  intro input result hs
  have ht : (embed result.1, result.2) ∈ (runToBoundary step targetBoundary fuel (embed input)).support := by
    rw [runToBoundary_map sourceStep step sourceBoundary targetBoundary embed hBoundary hStep,
      PMF.mem_support_map_iff]
    exact ⟨result, hs, rfl⟩
  exact runToBoundary_reachable step targetBoundary fuel (embed input) (embed result.1, result.2) ht

end Foundation.Probability.TimedExecution.Procedure
