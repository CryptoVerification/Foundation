import Foundation.Crypto.Semantics.Machine.Compiler
import Foundation.Crypto.Semantics.Machine.Adversary
import Foundation.Examples.BitMachineExecution
import Foundation.Examples.MachinePolynomialTime

namespace Machine.Examples

universe u v w

open GuardedCompiler

/-- The 291 finite instructions include actual raw-input preparation,
guarded execution, output extraction and the final halt. -/
example : (rawCompile randomOutputBit).length = 291 := by
  rw [rawCompile_length]
  rfl

example : rawTraceBudget (fun _ => 2) 0 = 363 := rfl
example : rawTraceBudget (fun _ => 2) 3 = 828 := rfl

example : HaltsWithin (rawCompile randomOutputBit) [] 363 :=
  rawCompile_haltsWithin randomOutputBit [] (fun _ => 2) randomOutputBit_haltsWithin

example : HaltsWithin (rawCompile randomOutputBit) [true, false, true] 828 :=
  rawCompile_haltsWithin randomOutputBit [true, false, true] (fun _ => 2)
    (randomOutputBit_haltsWithin_any _)

/-- Both fair outcomes are raw one-bit outputs. Neither the guarded
boundary nor the two-cell representation leaks into the protocol output. -/
example : evalWithin (rawCompile randomOutputBit) [] 363 =
    Foundation.Probability.sampleBit.map (fun bit => some [bit]) := by
  exact (rawCompile_evalWithin randomOutputBit [] (fun _ => 2) randomOutputBit_haltsWithin).trans
    randomOutputBit_eval

example : PolynomialTime (rawCompile randomOutputBit) :=
  rawCompile_polynomialTime randomOutputBit randomOutputBit_polynomialTime

/-- This theorem covers every finite raw input and all random branches. -/
example (source : Program) (h : PolynomialTime source) : PolynomialTime (rawCompile source) :=
  rawCompile_polynomialTime source h

example (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalWithin (rawCompile source) input (rawTraceBudget q input.length) =
      evalWithin source input (q input.length) :=
  rawCompile_evalWithin source input q halts

example (source : Program) (input : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalConfigWithin (rawCompile source) (Configuration.initial input) (rawTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map (rawResult source input) :=
  rawCompile_configuration_eval source input q halts

example (q : Nat → Nat) (m : Nat) :
    rawTraceBudget q m ≤ 125 * (m + 1) * (q m + 1) ^ 2 := rawTraceBudget_bound q m

/-- Caller-owned public data and protocol state stay outside the source's
guarded tapes, even when the source writes a random output bit. -/
example (savedInput savedOutput : List (Option Bool)) :
    evalConfigWithin (rawCompile randomOutputBit) (packInputStart savedInput savedOutput []) 363 =
      (evalConfigWithin randomOutputBit (preparedSource []) 2).map
        (rawResultFrom randomOutputBit [] savedInput savedOutput) :=
  rawCompile_configuration_eval_from randomOutputBit [] savedInput savedOutput
    (fun _ => 2) randomOutputBit_haltsWithin

example (source : Program) (input : List Bool)
    (savedInput savedOutput : List (Option Bool)) (c : Configuration) :
    (rawResultFrom source input savedInput savedOutput c).outputTape.left.drop
      c.outputBits.length = savedOutput :=
  (rawResultFrom_preserves_saved_data source input savedInput savedOutput c).2

/-- The generated guarded source can be called inside a randomized
wrapper. The return distribution retains full tape and head information. -/
example (pre suffix : Program) (returnPc : Nat) (source : Program)
    (hLayout : ∀ pc, pc ≤ (rawCompile source).length → pre.length + pc ≠ returnPc)
    (input : List Bool) (savedInput savedOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalReturnWithin (Program.withSubroutine pre (rawCompile source) suffix returnPc) returnPc
      ((packInputStart savedInput savedOutput input).rebasePc pre.length)
      (rawTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (fun c => (rawResultFrom source input savedInput savedOutput c).resumeAt returnPc) :=
  rawCompile_withSubroutine_return_eval pre suffix returnPc source hLayout input
    savedInput savedOutput q halts

/-- The compiler is an explicit finite syntax constructor. Its bitstring
interpreter rejects invalid codes and emits the encoded transformed code. -/
example (source : Program) : ProgramCompiler.guarded.runCode (Program.encode source) =
    some (Program.encode (rawCompile source)) := ProgramCompiler.runCode_encode .guarded source

/-- One transformed finite program realizes the entire family through
any existing finite-I/O adapter. The source budget must genuinely halt on
every input; an invalid timeout budget is not a simulation certificate. -/
example {P : CryptoGoal.{u}} (J : MachineAdversaryInterface.{u, v, w} P)
    (F : InstanceFamily P) (source : Program) (q : Nat → Nat)
    (halts : ∀ input, HaltsWithin source input (q input.length)) :
    J.realizeFamily F (rawCompile source) (rawTraceBudget q) = J.realizeFamily F source q := by
  funext n
  unfold MachineAdversaryInterface.realizeFamily
  congr 1
  funext request
  unfold MachineAdversaryInterface.responseWithin
  dsimp only
  rw [rawCompile_evalWithin source (J.machineInput n (F n) request) q (halts _)]

end Machine.Examples
