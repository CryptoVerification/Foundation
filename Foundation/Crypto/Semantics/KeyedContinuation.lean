import Foundation.Crypto.Semantics.ProcedurePublicComposition

/-! A retained key may be used after a public prefix independent of it.
Only the key-averaged suffix must be secure: individual keys need not have
identical ciphertext distributions. Public prefix states and total costs
remain in the conclusion. -/
namespace Foundation.Probability.KeyedContinuation
universe u v w
variable {Key : Type u} {Public : Type v} {Observed : Type w}

noncomputable def compose (keys : PMF Key) (before : Key → PMF (Public × Nat))
    (suffix : Key → Public → PMF (Observed × Nat)) : PMF ((Public × Observed) × Nat) :=
  keys.bind fun key => (before key).bind fun first =>
    (suffix key first.1).map fun second => ((first.1, second.1), first.2 + second.2)

/-- Prefix independence allows the same sampled key to be averaged in the
suffix conditional on each public state. The prefix cost is also retained. -/
theorem compose_independent (keys : PMF Key) (before : Key → PMF (Public × Nat))
    (suffix : Key → Public → PMF (Observed × Nat))
    (commonPrefix : PMF (Public × Nat)) (commonSuffix : Public → PMF (Observed × Nat))
    (hPrefix : ∀ key, before key = commonPrefix)
    (hSuffix : ∀ state, keys.bind (fun key => suffix key state) = commonSuffix state) :
    compose keys before suffix = commonPrefix.bind (fun first =>
      (commonSuffix first.1).map (fun second => ((first.1, second.1), first.2 + second.2))) := by
  unfold compose
  simp_rw [hPrefix]
  rw [PMF.bind_comm]
  congr 1
  funext first
  have h := congrArg (fun distribution => distribution.map
    (fun second => ((first.1, second.1), first.2 + second.2))) (hSuffix first.1)
  simpa only [PMF.map_bind] using h

/-- Two secure suffix games remain equal after possibly different physical
prefix families with the same key-independent public cost distribution. -/
theorem compose_eq (keys : PMF Key) (leftPrefix rightPrefix : Key → PMF (Public × Nat))
    (leftSuffix rightSuffix : Key → Public → PMF (Observed × Nat))
    (commonPrefix : PMF (Public × Nat))
    (hLeft : ∀ key, leftPrefix key = commonPrefix)
    (hRight : ∀ key, rightPrefix key = commonPrefix)
    (hSuffix : ∀ state, keys.bind (fun key => leftSuffix key state) =
      keys.bind (fun key => rightSuffix key state)) :
    compose keys leftPrefix leftSuffix = compose keys rightPrefix rightSuffix := by
  rw [compose_independent keys leftPrefix leftSuffix commonPrefix
    (fun state => keys.bind (fun key => leftSuffix key state)) hLeft (fun _ => rfl)]
  rw [compose_independent keys rightPrefix rightSuffix commonPrefix
    (fun state => keys.bind (fun key => leftSuffix key state)) hRight (fun state => (hSuffix state).symm)]

end Foundation.Probability.KeyedContinuation

namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x y z
variable {Key : Type u} {State : Type v} {Input : Type w} {Middle : Type x}
    {Output : Type y} {Observed : Type z} {step : Key → State → PMF State}

/-- Key averaging of actual sequential contracts. Every key-specific
machine still satisfies physical handoff and both procedures are charged. -/
theorem keyed_seq_public_cost (keys : PMF Key)
    (first : ∀ key, Procedure (step key) Input Middle)
    (second : ∀ key, Procedure (step key) Middle Output)
    (handoff : ∀ key input middle, middle ∈ ((first key).semantics input).support →
      (second key).entry middle = (first key).exit input middle)
    (cap : Key → Input → Nat)
    (hCap : ∀ key input middle, middle ∈ ((first key).semantics input).support →
      (second key).budget middle ≤ cap key input)
    (view : Key → Middle → Output → Observed) (input : Input)
    (commonPrefix : PMF (Middle × Nat)) (commonSuffix : Middle → PMF (Observed × Nat))
    (hPrefix : ∀ key, (first key).costed input = commonPrefix)
    (hSuffix : ∀ middle, keys.bind (fun key => ((second key).costed middle).map
      (fun result => (view key middle result.1, result.2))) = commonSuffix middle) :
    keys.bind (fun key =>
      (((first key).seq (second key) (handoff key) (cap key) (hCap key)).costed input).map
        (fun result => ((result.1.1, view key result.1.1 result.1.2), result.2))) =
      commonPrefix.bind (fun first => (commonSuffix first.1).map
        (fun second => ((first.1, second.1), first.2 + second.2))) := by
  have h := KeyedContinuation.compose_independent keys (fun key => (first key).costed input)
    (fun key middle => ((second key).costed middle).map
      (fun result => (view key middle result.1, result.2))) commonPrefix commonSuffix hPrefix hSuffix
  simpa only [KeyedContinuation.compose, Procedure.seq, PMF.map_bind, PMF.map_comp, Function.comp_def] using h

end Foundation.Probability.TimedExecution.Procedure
