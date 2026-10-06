import Foundation.Crypto.Semantics.Oracle.InteractiveMachine
import Foundation.Crypto.Semantics.Oracle.QuerySecurity

/-! Full attack runtime for the typed oracle goals. A single finite interactive
code implements the family, and its complete observable distribution matches
the typed experiment, including the transcript and final oracle state.
The time bound counts the whole interactive machine execution. -/

namespace CryptoOracle

open Foundation.Probability Machine
open scoped ENNReal

universe u v w

variable {Request Response State : Type u}

/-- Finite encodings of public inputs and oracle messages. Decoding and
encoding at the oracle boundary are challenger operations. Local transfer,
decision making and message construction are interactive machine operations. -/
structure WholeInterface (P : Protocol Request Response State) where
  instanceEncoding : ∀ n, FiniteBitEncoding (P.Instance n)
  requestEncoding : FiniteBitEncoding Request
  responseEncoding : FiniteBitEncoding Response
  fallbackRequest : Request

namespace WholeInterface

variable {P : Protocol Request Response State}

def input (J : WholeInterface P) (n : Nat) (I : P.Instance n) : List Bool :=
  encodeSecurityParameter n ++ frame ((J.instanceEncoding n).encode I)

noncomputable def bitOracle (J : WholeInterface P) (oracle : Oracle Request Response State) :
    Interactive.BitOracle State :=
  fun state bits =>
    (oracle state ((J.requestEncoding.decode bits).getD J.fallbackRequest)).map fun response =>
      (response.1, J.responseEncoding.encode response.2)

def encodeOutcome (J : WholeInterface P) (outcome : Outcome Request Response Bool State) :
    Interactive.Observation State :=
  ⟨some outcome.result, outcome.state,
    outcome.trace.map (fun (request, response) =>
      (J.requestEncoding.encode request, J.responseEncoding.encode response))⟩

def world (P : Protocol Request Response State) (n : Nat) (I : P.Instance n) (right : Bool) :
    Oracle Request Response State := if right then (P.games n I).right else (P.games n I).left

def initialState (P : Protocol Request Response State) (n : Nat) (I : P.Instance n)
    (right : Bool) : State :=
  if right then (P.games n I).rightInitial else (P.games n I).leftInitial

noncomputable def execution (J : WholeInterface P) (code : Interactive.Code)
    (n : Nat) (I : P.Instance n) (right : Bool) (fuel : Nat) :
    ProbComp (Interactive.Configuration State) :=
  Interactive.eval code (J.bitOracle (world P n I right))
    (Interactive.Configuration.initial (initialState P n I right) (J.input n I)) fuel

end WholeInterface

/-- One fixed code, outside the security-parameter quantifier, implements all
local computation. Both worlds must complete without timeout. The observable
law includes the entire encoded transcript, not just the output bit. -/
structure WholeWitness {P : Protocol Request Response State} (J : WholeInterface P)
    (time queries : Nat → Nat) (F : InstanceFamily (goal P))
    (A : AdversaryFamily (goal P) F) where
  code : Interactive.Code
  halts : ∀ n right,
    Interactive.HaltsWithin code (J.bitOracle (WholeInterface.world P n (F n) right))
      (Interactive.Configuration.initial (WholeInterface.initialState P n (F n) right)
        (J.input n (F n))) (time n)
  queries : ∀ n right (finish : Interactive.Configuration State),
    finish ∈ (J.execution code n (F n) right (time n)).support →
      finish.reverseTrace.length ≤ queries n
  realizes : ∀ n right,
    (J.execution code n (F n) right (time n)).map Interactive.observe =
      ((A n).run (WholeInterface.world P n (F n) right)
        (WholeInterface.initialState P n (F n) right)).map J.encodeOutcome

def wholeClass {P : Protocol Request Response State} (J : WholeInterface P)
    (time queries : Nat → Nat) : AdversaryClass (goal P) where
  admissible F A := Nonempty (WholeWitness J time queries F A)

def WholeSecure {P : Protocol Request Response State} (J : WholeInterface P)
    (time queries : Nat → Nat) (F : InstanceFamily (goal P)) (ε : Nat → ℝ≥0∞) : Prop :=
  BoundedByOnWithin (goal P) (wholeClass J time queries) F ε

namespace WholeWitness

variable {P : Protocol Request Response State} {J : WholeInterface P}
  {time queries : Nat → Nat} {F : InstanceFamily (goal P)}
  {A : AdversaryFamily (goal P) F}

/-- The query bound applies to the original typed experiment as well as to
the native implementation: realization preserves the entire transcript. -/
theorem trace_length_le (W : WholeWitness J time queries F A) (n : Nat) (right : Bool)
    (outcome : Outcome Request Response Bool State)
    (hSupport : outcome ∈ ((A n).run (WholeInterface.world P n (F n) right)
      (WholeInterface.initialState P n (F n) right)).support) :
    outcome.trace.length ≤ queries n := by
  have hEncoded : J.encodeOutcome outcome ∈
      (((A n).run (WholeInterface.world P n (F n) right)
        (WholeInterface.initialState P n (F n) right)).map J.encodeOutcome).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨outcome, hSupport, rfl⟩
  rw [← W.realizes n right, PMF.mem_support_map_iff] at hEncoded
  obtain ⟨finish, hFinish, hEq⟩ := hEncoded
  have hLength := congrArg (fun o : Interactive.Observation State => o.trace.length) hEq
  have hLength' : finish.reverseTrace.length = outcome.trace.length := by
    simpa [Interactive.observe, WholeInterface.encodeOutcome] using hLength
  rw [← hLength']
  exact W.queries n right finish hFinish

/-- Increasing the time bound preserves the full distribution. It cannot
change the attack by changing the experiment's fuel. -/
def mono (W : WholeWitness J time queries F A)
    (time' queries' : Nat → Nat) (ht : ∀ n, time n ≤ time' n)
    (hq : ∀ n, queries n ≤ queries' n) : WholeWitness J time' queries' F A where
  code := W.code
  halts := fun n right => (W.halts n right).mono (ht n)
  queries := by
    intro n right finish hFinish
    have heq := Interactive.eval_stable W.code
      (J.bitOracle (WholeInterface.world P n (F n) right))
      (Interactive.Configuration.initial (WholeInterface.initialState P n (F n) right)
        (J.input n (F n))) (time n) (time' n - time n) (W.halts n right)
    rw [Nat.add_sub_of_le (ht n)] at heq
    change finish ∈ (Interactive.eval W.code
      (J.bitOracle (WholeInterface.world P n (F n) right))
      (Interactive.Configuration.initial (WholeInterface.initialState P n (F n) right)
        (J.input n (F n))) (time' n)).support at hFinish
    rw [heq] at hFinish
    exact (W.queries n right finish hFinish).trans (hq n)
  realizes := by
    intro n right
    have heq := Interactive.eval_stable W.code
      (J.bitOracle (WholeInterface.world P n (F n) right))
      (Interactive.Configuration.initial (WholeInterface.initialState P n (F n) right)
        (J.input n (F n))) (time n) (time' n - time n) (W.halts n right)
    rw [Nat.add_sub_of_le (ht n)] at heq
    change (Interactive.eval W.code
      (J.bitOracle (WholeInterface.world P n (F n) right))
      (Interactive.Configuration.initial (WholeInterface.initialState P n (F n) right)
        (J.input n (F n))) (time' n)).map Interactive.observe = _
    rw [heq]
    exact W.realizes n right

end WholeWitness

theorem WholeSecure.mono {P : Protocol Request Response State} {J : WholeInterface P}
    {time time' queries queries' : Nat → Nat}
    {F : InstanceFamily (goal P)} {ε δ : Nat → ℝ≥0∞}
    (h : WholeSecure J time' queries' F ε) (ht : ∀ n, time n ≤ time' n)
    (hq : ∀ n, queries n ≤ queries' n) (hεδ : ∀ n, ε n ≤ δ n) :
    WholeSecure J time queries F δ := by
  intro A ⟨W⟩ n
  exact (h A ⟨W.mono time' queries' ht hq⟩ n).trans (hεδ n)

/-- A reduction's executable part receives only finite interactive code.
The mapped witness must certify precisely that compiler's output. -/
structure WholeReduction {Request' Response' State' : Type v}
    (P : Protocol Request Response State) (Q : Protocol Request' Response' State')
    (r : Reduction (goal P) (goal Q)) (JP : WholeInterface P) (JQ : WholeInterface Q)
    (sourceTime sourceQueries targetTime targetQueries : Nat → Nat) where
  compiler : Interactive.Compiler
  mapWitness : ∀ (F : InstanceFamily (goal P)) (A : AdversaryFamily (goal P) F),
    WholeWitness JP sourceTime sourceQueries F A →
      WholeWitness JQ targetTime targetQueries (r.mapFamily F) (r.mapAdversaryFamily F A)
  code_eq : ∀ F A W, (mapWitness F A W).code = compiler.run W.code

namespace WholeReduction

variable {Request' Response' State' : Type v}
  {P : Protocol Request Response State} {Q : Protocol Request' Response' State'}
  {r : Reduction (goal P) (goal Q)} {JP : WholeInterface P} {JQ : WholeInterface Q}
  {sourceTime sourceQueries targetTime targetQueries : Nat → Nat}

theorem compiler_halts
    (T : WholeReduction P Q r JP JQ sourceTime sourceQueries targetTime targetQueries)
    (F : InstanceFamily (goal P)) (A : AdversaryFamily (goal P) F)
    (W : WholeWitness JP sourceTime sourceQueries F A) (n : Nat) (right : Bool) :
    Interactive.HaltsWithin (T.compiler.run W.code)
      (JQ.bitOracle (WholeInterface.world Q n (r.mapFamily F n) right))
      (Interactive.Configuration.initial
        (WholeInterface.initialState Q n (r.mapFamily F n) right)
        (JQ.input n (r.mapFamily F n))) (targetTime n) := by
  rw [← T.code_eq F A W]
  exact (T.mapWitness F A W).halts n right

theorem realizes_emitted
    (T : WholeReduction P Q r JP JQ sourceTime sourceQueries targetTime targetQueries)
    (F : InstanceFamily (goal P)) (A : AdversaryFamily (goal P) F)
    (W : WholeWitness JP sourceTime sourceQueries F A) (n : Nat) (right : Bool) :
    (JQ.execution (T.compiler.run W.code) n (r.mapFamily F n) right (targetTime n)).map
      Interactive.observe =
      ((r.mapAdversaryFamily F A n).run
        (WholeInterface.world Q n (r.mapFamily F n) right)
        (WholeInterface.initialState Q n (r.mapFamily F n) right)).map JQ.encodeOutcome := by
  rw [← T.code_eq F A W]
  exact (T.mapWitness F A W).realizes n right

theorem secure (T : WholeReduction P Q r JP JQ sourceTime sourceQueries targetTime targetQueries)
    (F : InstanceFamily (goal P)) (ε : Nat → ℝ≥0∞)
    (h : WholeSecure JQ targetTime targetQueries (r.mapFamily F) ε) :
    WholeSecure JP sourceTime sourceQueries F (fun n => r.loss.eval n (ε n)) := by
  intro A ⟨W⟩ n
  exact (r.advantageProfile_le F A n).trans
    (r.loss.monotone n (h _ ⟨T.mapWitness F A W⟩ n))

noncomputable def id (J : WholeInterface P) (time queries : Nat → Nat) :
    WholeReduction P P (Reduction.id (goal P)) J J time queries time queries where
  compiler := .identity
  mapWitness := fun _ _ W => W
  code_eq := by intro F A W; rfl

noncomputable def comp {Request'' Response'' State'' : Type w}
    {S : Protocol Request'' Response'' State''} {s : Reduction (goal Q) (goal S)}
    {JS : WholeInterface S} {finalTime finalQueries : Nat → Nat}
    (T : WholeReduction P Q r JP JQ sourceTime sourceQueries targetTime targetQueries)
    (U : WholeReduction Q S s JQ JS targetTime targetQueries finalTime finalQueries) :
    WholeReduction P S (r.comp s) JP JS sourceTime sourceQueries finalTime finalQueries where
  compiler := .comp T.compiler U.compiler
  mapWitness := fun F A W => U.mapWitness (r.mapFamily F) (r.mapAdversaryFamily F A)
    (T.mapWitness F A W)
  code_eq := by
    intro F A W
    rw [U.code_eq, T.code_eq]
    rfl

end WholeReduction
end CryptoOracle
