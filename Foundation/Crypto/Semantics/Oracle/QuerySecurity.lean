import Foundation.Crypto.Semantics.Oracle.Program
import Foundation.Crypto.Semantics.Machine.ResourceReduction

/-! Query-restricted oracle indistinguishability and concrete reduction rules.
The goal's advantage executes the same explicit oracle program whose calls
are certified by `BoundedQueries`. Machine resources retain their existing
one-request interpretation; host continuation costs are not silently charged. -/

namespace CryptoOracle

open Foundation.Probability Machine
open scoped ENNReal

universe u v w a b c d e f

/-- The adversary sees responses but does not receive either hidden state.
Each world retains its own state across all adaptive calls. The two hidden
state types may differ; the default retains same-state protocols. -/
structure GamePair (Request Response State : Type u) (RightState : Type u := State) where
  left : Oracle Request Response State
  right : Oracle Request Response RightState
  leftInitial : State
  rightInitial : RightState

/-- Public instances are separate from the experiment's oracle functions.
They can therefore have finite encodings without encoding arbitrary PMFs. -/
structure Protocol (Request Response State : Type u) (RightState : Type u := State) where
  Instance : Nat → Type u
  games : ∀ n, Instance n → GamePair Request Response State RightState

variable {Request Response State RightState : Type u}

noncomputable def goal (P : Protocol Request Response State RightState) : CryptoGoal.{u} where
  Instance := P.Instance
  Adversary := fun _ _ => Program Request Response Bool
  advantage n I A := probabilityGap
    (eventProb ((A.run (P.games n I).left (P.games n I).leftInitial).map Outcome.result)
      (· = true))
    (eventProb ((A.run (P.games n I).right (P.games n I).rightInitial).map Outcome.result)
      (· = true))

def queryClass (P : Protocol Request Response State RightState) (q : Nat → Nat) :
    AdversaryClass (goal P) where
  admissible _ A := ∀ n, (A n).BoundedQueries (q n)

/-- No-query adversaries have zero distinguishing advantage in every pair
of oracle experiments, even if they draw local random coins. -/
theorem zeroQueries_secure (P : Protocol Request Response State RightState)
    (F : InstanceFamily (goal P)) :
    BoundedByOnWithin (goal P) (queryClass P (fun _ => 0)) F (fun _ => 0) := by
  intro A hA n
  change probabilityGap _ _ ≤ 0
  rw [(hA n).zero_run_result_eq (P.games n (F n)).left (P.games n (F n)).right
    (P.games n (F n)).leftInitial (P.games n (F n)).rightInitial]
  simp [probabilityGap]

/-- Concrete `(resource bounds, query bound, advantage bound)` security.
Both conditions concern the same adversary family. -/
def ResourceQuerySecure {Request Response State RightState : Type u}
    {P : Protocol Request Response State RightState}
    (J : MachineAdversaryInterface.{u, a, b} (goal P))
    (R : ResourceBounds) (q : Nat → Nat)
    (F : InstanceFamily (goal P)) (ε : Nat → ℝ≥0∞) : Prop :=
  BoundedByOnWithin (goal P)
    ((J.resourceClass R).inter (queryClass P q)) F ε

theorem ResourceQuerySecure.mono {Request Response State RightState : Type u}
    {P : Protocol Request Response State RightState}
    {J : MachineAdversaryInterface.{u, a, b} (goal P)}
    {R S : ResourceBounds} {q q' : Nat → Nat}
    {F : InstanceFamily (goal P)} {ε δ : Nat → ℝ≥0∞}
    (h : ResourceQuerySecure J S q' F ε) (hRS : R.LE S)
    (hqq' : ∀ n, q n ≤ q' n) (hεδ : ∀ n, ε n ≤ δ n) :
    ResourceQuerySecure J R q F δ := by
  intro A hA n
  exact (h A ⟨hA.1.mono hRS, fun m => (hA.2 m).mono (hqq' m)⟩ n).trans (hεδ n)

/-- The query part of admissibility bounds actual execution in either world. -/
theorem admitted_trace_length_le {Request Response State RightState : Type u}
    {P : Protocol Request Response State RightState}
    {J : MachineAdversaryInterface.{u, a, b} (goal P)}
    {R : ResourceBounds} {q : Nat → Nat}
    {F : InstanceFamily (goal P)}
    {A : AdversaryFamily (goal P) F}
    (h : ((J.resourceClass R).inter (queryClass P q)).admissible F A)
    (n : Nat) (oracle : Oracle Request Response State) (state : State)
    (outcome : Outcome Request Response Bool State)
    (hSupport : outcome ∈ ((A n).run oracle state).support) :
    outcome.trace.length ≤ q n :=
  (h.2 n).trace_length_le oracle state outcome hSupport

/-- Uniform machine resources and query preservation are separate obligations.
Query preservation is about the program executed by the target security goal. -/
structure QueryReduction
    {Request Response State RightState : Type u} {Request' Response' State' RightState' : Type v}
    (P : Protocol Request Response State RightState) (Q : Protocol Request' Response' State' RightState')
    (r : Reduction (goal P) (goal Q))
    (JP : MachineAdversaryInterface.{u, a, b} (goal P))
    (JQ : MachineAdversaryInterface.{v, c, d} (goal Q))
    (source target : ResourceBounds) (sourceQueries targetQueries : Nat → Nat) where
  machine : r.ResourceProgramReduction JP JQ source target
  queries : r.PreservesAdmissibility
    (queryClass P sourceQueries)
    (queryClass Q targetQueries)

namespace QueryReduction

variable {Request Response State RightState : Type u} {Request' Response' State' RightState' : Type v}
  {P : Protocol Request Response State RightState} {Q : Protocol Request' Response' State' RightState'}
  {r : Reduction (goal P) (goal Q)}
  {JP : MachineAdversaryInterface.{u, a, b} (goal P)}
  {JQ : MachineAdversaryInterface.{v, c, d} (goal Q)}
  {source target : ResourceBounds} {sourceQueries targetQueries : Nat → Nat}

theorem secure (T : QueryReduction P Q r JP JQ source target sourceQueries targetQueries)
    (F : InstanceFamily (goal P)) (ε : Nat → ℝ≥0∞)
    (h : ResourceQuerySecure JQ target targetQueries (r.mapFamily F) ε) :
    ResourceQuerySecure JP source sourceQueries F (fun n => r.loss.eval n (ε n)) := by
  intro A hA n
  have hMapped := h (r.mapAdversaryFamily F A)
    ⟨T.machine.mapWithin hA.1, T.queries.preserves F A hA.2⟩ n
  exact (r.advantageProfile_le F A n).trans (r.loss.monotone n hMapped)

noncomputable def id (J : MachineAdversaryInterface.{u, a, b} (goal P))
    (R : ResourceBounds) (q : Nat → Nat) :
    QueryReduction P P (Reduction.id (goal P)) J J R R q q where
  machine := Reduction.ResourceProgramReduction.id J R
  queries := Reduction.id_preservesAdmissibility _ _

noncomputable def comp {Request'' Response'' State'' RightState'' : Type w}
    {S : Protocol Request'' Response'' State'' RightState''}
    {s : Reduction (goal Q) (goal S)}
    {JS : MachineAdversaryInterface.{w, e, f} (goal S)}
    {final : ResourceBounds} {finalQueries : Nat → Nat}
    (T : QueryReduction P Q r JP JQ source target sourceQueries targetQueries)
    (U : QueryReduction Q S s JQ JS target final targetQueries finalQueries) :
    QueryReduction P S (r.comp s) JP JS source final sourceQueries finalQueries where
  machine := T.machine.comp U.machine
  queries := Reduction.comp_preservesAdmissibility r s _ _ _ T.queries U.queries

end QueryReduction
end CryptoOracle
