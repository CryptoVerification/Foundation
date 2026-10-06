import Foundation.Constructions.Symmetric.PRFCounterLogic
import Foundation.Examples.CounterMasking

namespace CryptoOracle.CounterWholeExamples
open Foundation.Probability CounterMasking CounterMasking.Whole
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-- A native attack remains valid and terminates for either pad bit. Its
input is arbitrary; the finite code reads only the ciphertext output tape. -/
theorem one_safe (input : List Bool) (side bit : Bool) (pad : List Bool → List Bool)
    (hp : pad [false] = [bit]) :
    Safe (compile side CounterMaskingExamples.attack) pad 1 27 (initial input [true]) := by
  cases side <;> cases bit
  all_goals
    repeat' (
      rw [Safe]
      constructor
      case left =>
        simp [WellFormed, initial, Interactive.Configuration.initial,
          Interactive.transition, CounterMaskingExamples.attack, compile,
          Machine.Configuration.initial, Machine.Instruction.next,
          Machine.Configuration.updateTape, Machine.Configuration.advance,
          Machine.Configuration.tape, Machine.Tape.write, Machine.Tape.moveRight,
          Machine.Tape.moveLeft, fail, succeed, selectList, xorList, hp]
        first | exact ⟨[false], [true], rfl, rfl, rfl⟩ | skip
      intro next hn
      simp [sourceStep, Interactive.transition, CounterMaskingExamples.attack, compile,
          initial, Interactive.Configuration.initial, Machine.Configuration.initial,
          Machine.Instruction.next, Machine.Configuration.updateTape,
          Machine.Configuration.advance, Machine.Configuration.tape,
          Machine.Tape.write, Machine.Tape.moveRight, Machine.Tape.moveLeft,
          fail, succeed, selectList, xorList, hp] at hn
      subst next)
    all_goals simp [Safe, complete, Interactive.Configuration.complete]


/-- The native execution actually makes a call and returns the ciphertext bit. -/
def final (side bit : Bool) : Configuration :=
  { source := ⟨(), .finished (Bool.xor side bit),
      [([false, true], [true, false, Bool.xor side bit])]⟩,
    capacity := [], counter := [true], phase := .source,
    reverseTrace := [([false], [bit])] }

theorem one_run (input : List Bool) (side bit : Bool) (pad : List Bool → List Bool)
    (hp : pad [false] = [bit]) :
    sourceRun (compile side CounterMaskingExamples.attack) pad 27 (initial input [true]) =
      PMF.pure (final side bit) := by
  cases side <;> cases bit
  all_goals
    repeat' (
      conv_lhs => rw [sourceRun]
      simp [sourceStep, Interactive.transition, CounterMaskingExamples.attack, compile,
        initial, Interactive.Configuration.initial, Machine.Configuration.initial,
        Machine.Instruction.next, Machine.Configuration.updateTape,
        Machine.Configuration.advance, Machine.Configuration.tape,
        Machine.Tape.write, Machine.Tape.moveRight, Machine.Tape.moveLeft,
        fail, succeed, selectList, xorList, hp, PMF.pure_bind])
    rfl

open Foundation.Symmetric Foundation.Symmetric.PRFCounter
open Foundation.Symmetric.PRFCounter.Resource
open CryptoLogic.General

/-- A deliberately insecure fixture; only the conditional security theorem
is used. The function domain grows, while the native attack code is fixed. -/
noncomputable def scheme : Scheme where
  Key := fun _ => Unit
  capacity := fun n => n + 1
  length := fun _ => 1
  keygen := fun _ => PMF.pure ()
  evaluate := fun _ _ _ _ => false

def time : Nat → Nat := fun _ => 27
def allowance : Nat → Nat := fun _ => 1

def typedAttack : PRFCounter.Attack 1 :=
  .query ((fun _ => false), (fun _ => true)) (fun reply =>
    .done ((reply.map (fun c => c.2 0)).getD false))

private theorem pad_zero (n : Nat) (table : Fin (n + 1) → Bits 1) :
    padTable table [false] = [(table ⟨0, by omega⟩) 0] := by
  have h := padTable_unary table (⟨0, by omega⟩ : Fin (n + 1))
  simpa [Bits.toList, List.ofFn_succ] using h

theorem sourceExecution : SourceExecution scheme time allowance
    CounterMaskingExamples.attack where
  timePoly := PolynomiallyBounded.const 27
  lengthPoly := PolynomiallyBounded.const 1
  queriesPoly := PolynomiallyBounded.const 1
  safe := by
    intro n side table
    change Safe (compile side CounterMaskingExamples.attack) (padTable table) 1 27
      (initial (Machine.encodeSecurityParameter n) [true])
    exact one_safe _ side _ _ (pad_zero n table)
  queries := by
    intro n side table out ho
    change out ∈ (sourceRun (compile side CounterMaskingExamples.attack) (padTable table)
      27 (initial (Machine.encodeSecurityParameter n) [true])).support at ho
    rw [one_run _ side _ _ (pad_zero n table), PMF.mem_support_pure_iff] at ho
    subst out
    exact Nat.le_refl 1

theorem sourceRealization : SourceRealization scheme time allowance
    (fun _ => typedAttack) CounterMaskingExamples.attack where
  law := by
    intro n side table
    change Fin (n + 1) → Bits 1 at table
    change (sourceRun (compile side CounterMaskingExamples.attack) (padTable table)
      27 (initial (Machine.encodeSecurityParameter n) [true])).map result =
      (runTable typedAttack side table).map some
    rw [one_run _ side _ _ (pad_zero n table)]
    simp [PMF.pure_map, result, final, runTable, typedAttack, Program.run,
      oracle, encrypt, selected, Bits.xor, scheme, Interactive.Configuration.result]
    cases side <;> simp [Bool.xor_comm]
  typedQueries := fun _ => .query _ _ 0 (fun _ => .done _ 0)

noncomputable def sourceWitness :
    (sourceObject scheme time allowance).Witness (fun _ => ()) (fun _ => typedAttack) where
  code := CounterMaskingExamples.attack
  resources := ()
  executes := sourceExecution
  realizes := sourceRealization
  admissible := ⟨CounterMaskingExamples.attack, sourceExecution, sourceRealization⟩

example (side : Bool) : TargetExecution scheme (reductionTime scheme time) allowance
    (compile side CounterMaskingExamples.attack) :=
  compiled_execution scheme time allowance side _ sourceExecution

example (side : Bool) : TargetRealization scheme (reductionTime scheme time) allowance
    (fun _ => reduce side 0 typedAttack) (compile side CounterMaskingExamples.attack) :=
  compiled_realization scheme time allowance side _ _ sourceExecution sourceRealization

/-- Every extracted certificate refers to exactly the emitted executable code. -/
example :
    ((Logic.sharedDerivation scheme time allowance).runWitnesses
      (fun _ => typedAttack) sourceWitness).map CertifiedOutput.emitted =
    [(0, ⟨Kind.target, compile false CounterMaskingExamples.attack⟩),
     (0, ⟨Kind.target, compile true CounterMaskingExamples.attack⟩)] := by
  rw [Derivation.runWitnesses_emitted]
  exact Logic.run scheme time allowance CounterMaskingExamples.attack

/-- The conservative certified whole-program budget is 1809 transitions. -/
example (n : Nat) : reductionTime scheme time n = 1809 := rfl

def emittedPrograms (output : List (Nat × Sigma system.Code)) :
    List (Nat × CounterMasking.Code) :=
  output.filterMap fun (i, code) => match code with
    | ⟨Kind.target, program⟩ => some (i, program)
    | _ => none

/-- info: true -/
#guard_msgs in
#eval emittedPrograms ((Logic.sharedDerivation scheme time allowance).run
    CounterMaskingExamples.attack) ==
  [(0, compile false CounterMaskingExamples.attack),
   (0, compile true CounterMaskingExamples.attack)]

/-- info: [(some false, 39, 1), (some true, 39, 1)] -/
#guard_msgs in
#eval (emittedPrograms ((Logic.sharedDerivation scheme time allowance).run
    CounterMaskingExamples.attack)).map fun (_, code) =>
  let (out, used) := simulate code CounterMaskingExamples.pad false
    1809 (initial (Machine.encodeSecurityParameter 3) [true])
  (result out, used, out.reverseTrace.length)

/-- info: [(none, 38), (none, 38)] -/
#guard_msgs in
#eval (emittedPrograms ((Logic.sharedDerivation scheme time allowance).run
    CounterMaskingExamples.attack)).map fun (_, code) =>
  let (out, used) := simulate code CounterMaskingExamples.pad false 38 (initial (Machine.encodeSecurityParameter 3) [true])
  (result out, used)


/-- The first ciphertext bit becomes the next left plaintext. The right
plaintext is zero, so the second request genuinely depends on the reply. -/
def adaptiveNative : Interactive.Code :=
  [.native (.write .output false), .native (.moveRight .output),
   .native (.write .output true), .native (.moveLeft .output), .call,
   .native (.moveRight .output), .native (.moveRight .output),
   .native (.moveRight .output), .native (.write .output false),
   .native (.moveLeft .output), .call,
   .native (.moveRight .output), .native (.moveRight .output),
   .native (.moveRight .output), .native .halt]

def adaptivePad (request : List Bool) : List Bool := [request = [false]]

/-- info: (some true, 81, [([false], [true]), ([true, false], [false])],
  [([false, true], [true, false, true]), ([true, false], [true, true, false, true])]) -/
#guard_msgs in
#eval (simulate (compile false adaptiveNative) adaptivePad false 300
  (initial [] [true, true])) |> fun (out, used) =>
    (result out, used, out.reverseTrace.reverse, out.source.reverseTrace.reverse)

/-- info: (some false, 81, [([false], [true]), ([true, false], [false])],
  [([false, true], [true, false, false]), ([false, false], [true, true, false, false])]) -/
#guard_msgs in
#eval (simulate (compile true adaptiveNative) adaptivePad false 300
  (initial [] [true, true])) |> fun (out, used) =>
    (result out, used, out.reverseTrace.reverse, out.source.reverseTrace.reverse)

/-- Source safety is proved for both responses and both message worlds. -/
theorem adaptive_safe (input : List Bool) (side bit₀ bit₁ : Bool)
    (pad : List Bool → List Bool) (h₀ : pad [false] = [bit₀])
    (h₁ : pad [true, false] = [bit₁]) :
    Safe (compile side adaptiveNative) pad 1 55 (initial input [true, true]) := by
  cases side <;> cases bit₀ <;> cases bit₁
  all_goals
    repeat' (
      rw [Safe]
      constructor
      case left =>
        simp [WellFormed, initial, Interactive.Configuration.initial,
          Interactive.transition, adaptiveNative, compile,
          Machine.Configuration.initial, Machine.Instruction.next,
          Machine.Configuration.updateTape, Machine.Configuration.advance,
          Machine.Configuration.tape, Machine.Tape.write, Machine.Tape.moveRight,
          Machine.Tape.moveLeft, fail, succeed, selectList, xorList, h₀, h₁]
        first
        | exact ⟨[false], [true], rfl, rfl, rfl⟩
        | exact ⟨[false], [false], rfl, rfl, rfl⟩
        | exact ⟨[true], [false], rfl, rfl, rfl⟩
        | skip
      intro next hn
      simp [sourceStep, Interactive.transition, adaptiveNative, compile,
        initial, Interactive.Configuration.initial, Machine.Configuration.initial,
        Machine.Instruction.next, Machine.Configuration.updateTape,
        Machine.Configuration.advance, Machine.Configuration.tape,
        Machine.Tape.write, Machine.Tape.moveRight, Machine.Tape.moveLeft,
        fail, succeed, selectList, xorList, h₀, h₁] at hn
      subst next)
    all_goals simp [Safe, complete, Interactive.Configuration.complete]

def adaptiveFinal (side bit₀ bit₁ : Bool) : Configuration :=
  let first := Bool.xor side bit₀
  let last := Bool.xor (if side then false else first) bit₁
  { source := ⟨(), .finished last,
      [([first, false], [true, true, false, last]),
       ([false, true], [true, false, first])]⟩,
    capacity := [], counter := [true, true], phase := .source,
    reverseTrace := [([true, false], [bit₁]), ([false], [bit₀])] }

theorem adaptive_run (input : List Bool) (side bit₀ bit₁ : Bool)
    (pad : List Bool → List Bool) (h₀ : pad [false] = [bit₀])
    (h₁ : pad [true, false] = [bit₁]) :
    sourceRun (compile side adaptiveNative) pad 55 (initial input [true, true]) =
      PMF.pure (adaptiveFinal side bit₀ bit₁) := by
  cases side <;> cases bit₀ <;> cases bit₁
  all_goals
    repeat' (
      conv_lhs => rw [sourceRun]
      simp [sourceStep, Interactive.transition, adaptiveNative, compile,
        initial, Interactive.Configuration.initial, Machine.Configuration.initial,
        Machine.Instruction.next, Machine.Configuration.updateTape,
        Machine.Configuration.advance, Machine.Configuration.tape,
        Machine.Tape.write, Machine.Tape.moveRight, Machine.Tape.moveLeft,
        fail, succeed, selectList, xorList, h₀, h₁, PMF.pure_bind])
    rfl

/-- The full target law, including both traces, follows from source safety. -/
theorem adaptive_target_run (input : List Bool) (side bit₀ bit₁ : Bool)
    (pad : List Bool → List Bool) (h₀ : pad [false] = [bit₀])
    (h₁ : pad [true, false] = [bit₁]) :
    eval (compile side adaptiveNative) (bitOracle pad) (initial input [true, true]) 6765 =
      PMF.pure (adaptiveFinal side bit₀ bit₁) := by
  have h := Whole.run_map (compile side adaptiveNative) pad 1 55 input [true, true]
    (adaptive_safe input side bit₀ bit₁ pad h₀ h₁) id
  rw [adaptive_run input side bit₀ bit₁ pad h₀ h₁] at h
  simpa only [PMF.map_id, budget] using h

/-- info: [(none, 80, 2), (none, 80, 2)] -/
#guard_msgs in
#eval [false, true].map fun side =>
  let (out, used) := simulate (compile side adaptiveNative) adaptivePad false 80
    (initial [] [true, true])
  (result out, used, out.reverseTrace.length)

noncomputable def adaptiveScheme : Scheme where
  Key := fun _ => Unit
  capacity := fun n => n + 2
  length := fun _ => 1
  keygen := fun _ => PMF.pure ()
  evaluate := fun _ _ _ _ => false
def adaptiveTime : Nat → Nat := fun _ => 55
def adaptiveAllowance : Nat → Nat := fun _ => 2

def adaptiveTyped : PRFCounter.Attack 1 :=
  .query ((fun _ => false), (fun _ => true)) (fun first =>
    let bit := (first.map (fun c => c.2 0)).getD false
    .query ((fun _ => bit), (fun _ => false)) (fun second =>
      .done ((second.map (fun c => c.2 0)).getD false)))

private theorem adaptive_pad (n : Nat) (table : Fin (n + 2) → Bits 1) :
    padTable table [false] = [(table ⟨0, by omega⟩) 0] ∧
    padTable table [true, false] = [(table ⟨1, by omega⟩) 0] := by
  constructor
  · simpa [Bits.toList, List.ofFn_succ] using
      padTable_unary table (⟨0, by omega⟩ : Fin (n + 2))
  · simpa [Bits.toList, List.ofFn_succ] using
      padTable_unary table (⟨1, by omega⟩ : Fin (n + 2))

theorem adaptiveExecution : SourceExecution adaptiveScheme adaptiveTime adaptiveAllowance
    adaptiveNative where
  timePoly := PolynomiallyBounded.const 55
  lengthPoly := PolynomiallyBounded.const 1
  queriesPoly := PolynomiallyBounded.const 2
  safe := by
    intro n side table
    change Safe (compile side adaptiveNative) (padTable table) 1 55
      (initial (Machine.encodeSecurityParameter n) [true, true])
    exact adaptive_safe _ side _ _ _ (adaptive_pad n table).1 (adaptive_pad n table).2
  queries := by
    intro n side table out ho
    change out ∈ (sourceRun (compile side adaptiveNative) (padTable table)
      55 (initial (Machine.encodeSecurityParameter n) [true, true])).support at ho
    rw [adaptive_run _ side _ _ _ (adaptive_pad n table).1 (adaptive_pad n table).2,
      PMF.mem_support_pure_iff] at ho
    subst out
    exact Nat.le_refl 2

theorem adaptiveRealization : SourceRealization adaptiveScheme adaptiveTime adaptiveAllowance
    (fun _ => adaptiveTyped) adaptiveNative where
  law := by
    intro n side table
    change Fin (n + 2) → Bits 1 at table
    change (sourceRun (compile side adaptiveNative) (padTable table)
      55 (initial (Machine.encodeSecurityParameter n) [true, true])).map result =
      (runTable adaptiveTyped side table).map some
    rw [adaptive_run _ side _ _ _ (adaptive_pad n table).1 (adaptive_pad n table).2]
    simp [PMF.pure_map, result, adaptiveFinal, runTable, adaptiveTyped, Program.run,
      oracle, encrypt, selected, Bits.xor, Interactive.Configuration.result]
    cases side <;> simp [Bool.xor_comm]
  typedQueries := fun _ => .query _ _ 1 (fun _ => .query _ _ 0 (fun _ => .done _ 0))

noncomputable def adaptiveWitness :
    (sourceObject adaptiveScheme adaptiveTime adaptiveAllowance).Witness
      (fun _ => ()) (fun _ => adaptiveTyped) where
  code := adaptiveNative
  resources := ()
  executes := adaptiveExecution
  realizes := adaptiveRealization
  admissible := ⟨adaptiveNative, adaptiveExecution, adaptiveRealization⟩

example (side : Bool) : TargetExecution adaptiveScheme
    (reductionTime adaptiveScheme adaptiveTime) adaptiveAllowance (compile side adaptiveNative) :=
  compiled_execution adaptiveScheme adaptiveTime adaptiveAllowance side _ adaptiveExecution

example : ((Logic.sharedDerivation adaptiveScheme adaptiveTime adaptiveAllowance).runWitnesses
    (fun _ => adaptiveTyped) adaptiveWitness).map CertifiedOutput.emitted =
    [(0, ⟨Kind.target, compile false adaptiveNative⟩),
     (0, ⟨Kind.target, compile true adaptiveNative⟩)] := by
  rw [Derivation.runWitnesses_emitted]
  exact Logic.run _ _ _ _

end CryptoOracle.CounterWholeExamples
