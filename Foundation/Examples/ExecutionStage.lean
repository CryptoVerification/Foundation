import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacySourceObservation
import Foundation.Examples.EncryptThenMACRepeatedCallback

namespace Foundation.Probability.TimedExecution.StageExamples

-- One Boolean source step takes two physical transitions. The completed
-- source state takes no more transitions, even though its upper bound is 2.
noncomputable def targetStep : Nat → PMF Nat
  | 0 => PMF.pure 1
  | _ => PMF.pure 2

def embed (source : Bool) : Nat := if source then 2 else 0
noncomputable def sourceStep (_ : Bool) : PMF Bool := PMF.pure true

noncomputable def stage : (source : Bool) → Stage targetStep embed source
  | true => Stage.identity targetStep embed true
  | false =>
    { budget := 2
      outcome := PMF.pure (true, 2)
      bounded := by intro result h; simp only [PMF.mem_support_pure_iff] at h; subst result; exact Nat.le_refl _
      law := by
        intro horizon hh
        cases horizon with
        | zero => omega
        | succ horizon =>
            cases horizon with
            | zero => omega
            | succ horizon => simp [eval, targetStep, embed, PMF.pure_bind] }

theorem cap (source : Bool) : (stage source).budget ≤ 2 := by cases source <;> simp [stage, Stage.identity]
theorem distribution (source : Bool) : (stage source).outcome.map Prod.fst = sourceStep source := by
  cases source <;> simp [stage, Stage.identity, sourceStep, PMF.pure_map]

example : (Stage.iterate stage 2 cap 2 false).budget = 4 := Stage.iterate_budget stage 2 cap 2 false
example : (Stage.iterate stage 2 cap 2 false).outcome = PMF.pure (true, 2) := by
  simp [Stage.iterate, Stage.iterateAux, Stage.identity, Stage.resize, Stage.compose, stage,
    PMF.pure_bind, PMF.pure_map]

example (horizon : Nat) (h : 4 ≤ horizon) : eval targetStep horizon 0 = PMF.pure 2 := by
  have hf : ∀ final ∈ (eval sourceStep 2 false).support,
      targetStep (embed final) = PMF.pure (embed final) := by
    intro final hFinal
    simp [eval, sourceStep] at hFinal
    subst final
    rfl
  simpa [embed, eval, sourceStep, PMF.pure_bind, PMF.pure_map] using
    Stage.iterate_final_law stage 2 cap sourceStep distribution 2 false hf horizon h

end Foundation.Probability.TimedExecution.StageExamples

namespace Foundation.Symmetric.EncryptThenMAC.SourceExecutionExamples
open Machine PrivacyMachine Foundation.Probability

def haltCode : Source.Code := [.native .halt]
noncomputable def oracle (state : Nat) (_ : List Bool) : PMF (Nat × List Bool) := PMF.pure (state + 1, [])

theorem halt_source {width : Nat} (key : TableMAC.Key width) (input : List Bool) :
    ∀ final ∈ (TimedExecution.eval (logicalStep haltCode oracle key) 1 (logicalInitial 17 input)).support,
      CryptoOracle.Interactive.Reification.terminal final.control = true := by
  intro final hFinal
  simp [TimedExecution.eval, logicalStep, logicalInitial, haltCode,
    CryptoOracle.Interactive.Reification.terminal, CryptoOracle.Interactive.Reification.action,
    CryptoOracle.Interactive.transition, Configuration.initial, Instruction.next] at hFinal
  subst final
  rfl

example (input : List Bool) :
    HaltsWithin haltCode oracle (initial 17 [true, true, true, true] input) (executionBudget 2 1) := by
  exact initialized_source_haltsWithin haltCode oracle (fun _ => 2) 0 1 17 input
    (fun key _ => halt_source key input)

def sourceOracle (key : TableMAC.Key 2)
    (state : Nat × List (List Bool × List Bool)) (request : List Bool) :
    (Nat × List (List Bool × List Bool)) × List Bool :=
  let answer := RepeatedCallbackExamples.oracle state.1 request
  ((answer.1, (request, answer.2) :: state.2),
    AuthenticateResponse.encode ((decodeCiphertext answer.2).map (fun bit => (bit, TableMAC.sign key bit))))

-- Compare the existing source-machine evaluator with the real whole
-- reduction, including both transcript views and the external state.
#guard [false, true].all fun coin =>
  let key : TableMAC.Key 2 := (fun _ => coin, fun _ => coin)
  let start : CryptoOracle.Interactive.Configuration (Nat × List (List Bool × List Bool)) :=
    ⟨(0, []), .running (Configuration.initial []), []⟩
  let (source, sourceUsed) := CryptoOracle.Interactive.Reification.simulate
    RepeatedCallbackExamples.code (sourceOracle key) coin 1000 start
  let (target, targetUsed) := simulate RepeatedCallbackExamples.code RepeatedCallbackExamples.oracle coin 2000
    (initial 0 [true, true, true, true] [])
  match sourceView target with
  | some observed => sourceUsed == 66 && targetUsed == 359 &&
      (observed.state, observed.control, observed.reverseTrace) == (source.state, source.control, source.reverseTrace) &&
      CryptoOracle.Interactive.Reification.terminal source.control
  | none => false

end Foundation.Symmetric.EncryptThenMAC.SourceExecutionExamples
