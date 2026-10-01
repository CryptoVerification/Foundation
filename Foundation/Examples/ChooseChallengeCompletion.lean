import Foundation.Machine.ChooseChallengeCompletion
import Foundation.Machine.ChooseChallengeRuntime
import Foundation.Examples.NormalizationGuessCompletion
import Foundation.Constructions.ElGamal.Concrete

namespace Foundation.Examples.ChooseChallengeCompletion

open Machine Machine.GuardedCompiler
open Foundation.Examples.GuessCompletion
open Foundation.Examples.NormalizationGuessCompletion (emptyNormalizer emptyNormalizer_haltsWithin emptyNormalizer_correct)

def demoInput : List Bool :=
  encodeSecurityParameter 0 ++ frame [] ++
    frame (FiniteBitEncoding.delimit [] ++ FiniteBitEncoding.delimit [] ++ [])

def demoTailBudget : Nat := chooseChallengeTailBudget randomTaggedGuess
  (fun _ => 4) (fun _ => 6) (fun _ => 1) (fun _ => 4) 0 [] [] [] []
  (fun _ => []) (fun _ => []) (fun _ => []) (fun _ _ => [])

def demoBudget : Nat := chooseTraceBudget (fun _ => 4) 0 [] [] [false] + (demoTailBudget + 1)

def demoProgram : Program := chooseChallengeGuessCompile randomTaggedGuess emptyNormalizer [.halt] randomTaggedGuess

example : demoProgram.length = 2784 := by
  rw [demoProgram, chooseChallengeGuessCompile_length]
  rfl

private theorem emptyResult_correct (input : List Bool) :
    evalWithin [.halt] input 1 = PMF.pure (some []) := by
  simp [evalWithin, evalConfigWithin, stepPMF, next, Instruction.next, Configuration.initial,
    Configuration.outputBits, Tape.bits, PMF.pure_map, PMF.pure_bind]

/-- All stages run in ordinary execution from the initial encoded tuple.
The choose fixture has real random branches and returns malformed choose
replies; this fixture's six-step normalizer emits empty canonical fields.
The empty-result multiplication call is a protocol test, not a group claim. -/
theorem demo_eval :
    (evalConfigWithin demoProgram (Configuration.initial demoInput) demoBudget).map
      (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.bind (fun bit =>
        (evalConfigWithin randomTaggedGuess (preparedSource (guessFromProductRequest 0 [] [] [] [])) 4).map
          (fun c => (true, [taggedGuessValue c.outputBits == bit]))) := by
  have h := chooseChallengeGuessCompile_correct randomTaggedGuess emptyNormalizer [.halt] randomTaggedGuess
    (fun _ => 4) (fun _ => 6) (fun _ => 1) (fun _ => 4) 0 [] [] [] []
    false false [] [false] rfl rfl (fun _ => []) (fun _ => []) (fun _ => []) (fun _ _ => [])
    (randomTaggedGuess_haltsWithin _) emptyNormalizer_haltsWithin
    (fun _ _ => emptyNormalizer_correct _) (fun _ => haltInstruction_haltsWithin _)
    (fun _ _ _ => emptyResult_correct _) randomTaggedGuess_haltsWithin
  simpa only [PMF.bind_const, demoProgram, demoInput, demoBudget, demoTailBudget,
    List.append_nil, FiniteBitEncoding.delimit] using h

/-- A uniform numerical continuation bound follows from source storage and
the scalar runtime theorem, without enumerating an exponentially large
list of random branches during proof or machine execution. The deliberately
loose constant is a witness, not a claim of minimal runtime. -/
example : demoTailBudget ≤ 16530800000 := by
  apply chooseChallengeTailBudget_le
  intro c hc
  have hSize := preparedChooseBranch_size_le randomTaggedGuess
    (encodeSecurityParameter 0 ++ frame [] ++ frame [false]) 4 c hc
  have h := chooseChallengeBranchBudget_bound (fun _ => 6) (fun _ => 1) (fun _ => 4)
    (encodeSecurityParameter 0 ++ frame [] ++ frame [false]) 0 [] [] [] []
    (fun _ => []) (fun _ => []) (fun _ => []) (fun _ _ => []) c
  dsimp only at h
  have hRequest : (encodeSecurityParameter 0 ++ frame [] ++ frame [false]).length = 5 := rfl
  rw [hRequest] at hSize
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero] at h
  apply h.trans
  norm_num only
  omega

example : HaltsWithin demoProgram demoInput demoBudget := by
  intro c run
  have hm := (PMF.mem_support_map_iff (fun d : Configuration => (d.halted, d.outputBits)) _
    (c.halted, c.outputBits)).mpr ⟨c, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [demo_eval, PMF.mem_support_bind_iff] at hm
  obtain ⟨bit, _hb, hm⟩ := hm
  rw [PMF.mem_support_map_iff] at hm
  obtain ⟨d, _hd, heq⟩ := hm
  exact (congrArg Prod.fst heq).symm

/-- Reuse the existing independent-guess probability argument after native
choose, normalizer, challenge, multiplication, guess and cleanup have run. -/
example :
    (evalConfigWithin demoProgram (Configuration.initial demoInput) demoBudget).map
      (fun c => (c.halted, c.outputBits)) =
      Foundation.Probability.sampleBit.map (fun bit => (true, [bit])) := by
  rw [demo_eval]
  let source := evalConfigWithin randomTaggedGuess (preparedSource (guessFromProductRequest 0 [] [] [] [])) 4
  have h := congrArg (fun law : PMF Bool => law.map (fun bit => (true, [bit])))
    (ElGamal.independentGuess_game_eq (source.map (fun c => taggedGuessValue c.outputBits)))
  change (Foundation.Probability.sampleBit.bind fun bit =>
    source.bind (fun c => PMF.pure (true, [taggedGuessValue c.outputBits == bit]))) = _
  simpa only [PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def] using h

end Foundation.Examples.ChooseChallengeCompletion
