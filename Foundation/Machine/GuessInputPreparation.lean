import Foundation.Machine.GuessBodyPreparation
import Foundation.Machine.GuessRequestPreparation

namespace Machine

private def guessInputTuple (first second last : List Bool) : List Bool :=
  FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last

/-- The framed DDH tuple has a nonempty unary length header. This describes
its retained cells, not a machine instruction that computes or reloads them. -/
def guessInputTupleTail (first second last : List Bool) : List Bool :=
  List.replicate ((guessInputTuple first second last).length - 1) true ++
    false :: guessInputTuple first second last

theorem frame_guessInputTuple (first second last : List Bool) :
    frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) =
      true :: guessInputTupleTail first second last := by
  have hPositive : 0 < (guessInputTuple first second last).length := by
    simp [guessInputTuple, FiniteBitEncoding.delimit_length]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hPositive)
  change frame (guessInputTuple first second last) = true :: guessInputTupleTail first second last
  simp only [frame, guessInputTupleTail, hk,
    Nat.succ_eq_add_one, Nat.add_sub_cancel, List.replicate_succ, List.cons_append,
    List.append_assoc, List.nil_append]

/-- Join the actual raw-body return to the request constructor. All five
stored blocks, the body, and both tapes' blank padding are the very same
physical cells. No new adversary state, product, or public input is loaded. -/
theorem prepareGuessBodyFinish_request_layout (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (padding : Nat) :
    (prepareGuessBodyFinish before (List.replicate padding none) beforeOutput
      n instanceBits first second last reply message₀ message₁ state selected product).resumeAt 0 =
      prepareGuessRequestStart before beforeOutput n instanceBits (guessInputTupleTail first second last)
        reply (canonicalMessageBits message₀ message₁ state) selected product
        (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)) padding
        (instanceBits.length + 1 - (2*second.length + 1) - product.length) := by
  have hi := prepareGuessBodyFinish_input before (List.replicate padding none) beforeOutput
    n instanceBits first second last reply message₀ message₁ state selected product
  have ho := prepareGuessBodyFinish_output before (List.replicate padding none) beforeOutput
    n instanceBits first second last reply message₀ message₁ state selected product
  change ({ pc := 0, inputTape := _, outputTape := _, halted := false } : Configuration) = _
  rw [hi, ho, frame_guessInputTuple]
  simp [prepareGuessRequestStart, prepareGuessPrefixStart, restoreGuessInputStart,
    restoreStoredInputStart, List.append_assoc]

/-- Complete native guess-input construction from the actual post-product
configuration. The body and request stages are emitted once each as finite
subroutines. Every original native transition and the caller halt is charged. -/
def prepareGuessInput : Program :=
  prepareGuessBody.asSubroutine 0 175 ++ prepareGuessRequest.asSubroutine 175 359 ++ [.halt]

def prepareGuessInputStart (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (padding : Nat) : Configuration :=
  prepareGuessBodyStart before (List.replicate padding none) beforeOutput
    n instanceBits first second last reply message₀ message₁ state selected product

def prepareGuessInputFinish (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (padding : Nat) : Configuration :=
  { prepareGuessRequestFinish before beforeOutput n instanceBits (guessInputTupleTail first second last)
      reply (canonicalMessageBits message₀ message₁ state) selected product
      (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)) padding with pc := 359 }

def prepareGuessInputSteps (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool) : Nat :=
  prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected product +
    (prepareGuessRequestSteps n instanceBits (guessInputTupleTail first second last)
      reply (canonicalMessageBits message₀ message₁ state) selected product
      (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)) + 1)

/-- Ordinary execution of the full constructor, including immediate
continuation on early returns. Both subroutines are deterministic. The
stopping evaluator is used only to prove the ordinary transition law. -/
theorem prepareGuessInput_eval (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (padding : Nat) :
    evalConfigWithin prepareGuessInput
      (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
      (prepareGuessInputSteps n instanceBits first second last reply message₀ message₁ state selected product) =
      PMF.pure (prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding) := by
  let bodyFinish := prepareGuessBodyFinish before (List.replicate padding none) beforeOutput
    n instanceBits first second last reply message₀ message₁ state selected product
  let bodySteps := prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected product
  let rawBody := true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)
  let tupleTail := guessInputTupleTail first second last
  let canonical := canonicalMessageBits message₀ message₁ state
  let outputBlanks := instanceBits.length + 1 - (2*second.length + 1) - product.length
  let requestStart := prepareGuessRequestStart before beforeOutput n instanceBits tupleTail reply canonical selected product rawBody padding outputBlanks
  let requestFinish := prepareGuessRequestFinish before beforeOutput n instanceBits tupleTail reply canonical selected product rawBody padding
  let requestSteps := prepareGuessRequestSteps n instanceBits tupleTail reply canonical selected product rawBody
  let pre := prepareGuessBody.asSubroutine 0 175
  have hPre : pre.length = 175 := by simp [pre, Program.asSubroutine_length, prepareGuessBody_length]
  have hRaw := prepareGuessBody_withSubroutine_eval []
    (prepareGuessRequest.asSubroutine 175 359 ++ [.halt]) 175
    (by intro pc hpc; simp only [List.length_nil, Nat.zero_add, prepareGuessBody_length] at *; omega)
    before (List.replicate padding none) beforeOutput n instanceBits first second last reply message₀ message₁ state selected product
  change evalReturnWithin prepareGuessInput 175
    (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
    bodySteps = PMF.pure (bodyFinish.resumeAt 175) at hRaw
  have hEntry : bodyFinish.resumeAt 175 = requestStart.rebasePc pre.length := by
    have h := congrArg (fun c : Configuration => c.rebasePc 175)
      (prepareGuessBodyFinish_request_layout before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
    simpa [Configuration.resumeAt, Configuration.rebasePc, hPre, bodyFinish,
      requestStart, tupleTail, canonical, rawBody, outputBlanks] using h
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt pre prepareGuessRequest requestStart
    (by change 0 ≤ prepareGuessRequest.length; exact Nat.zero_le _) rfl requestSteps
    (prepareGuessRequest_haltsFrom before beforeOutput n instanceBits tupleTail reply canonical selected product rawBody
      padding outputBlanks (by dsimp [outputBlanks]; omega))
  dsimp only at hCall
  have hProgram : Program.withSubroutine pre prepareGuessRequest [.halt]
      (pre.length + prepareGuessRequest.length + 1) = prepareGuessInput := by
    simp only [Program.withSubroutine, hPre, prepareGuessRequest_length, pre, prepareGuessInput]
  rw [hProgram, ← hEntry, prepareGuessRequest_eval _ _ _ _ _ _ _ _ _ _ _ _
    (by dsimp [outputBlanks]; omega), PMF.pure_map] at hCall
  simp only [hPre, prepareGuessRequest_length, Nat.reduceAdd] at hCall
  change evalConfigWithin prepareGuessInput (bodyFinish.resumeAt 175) (requestSteps + 1) =
    PMF.pure (prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding) at hCall
  have hTail (extra : Nat) : evalConfigWithin prepareGuessInput (bodyFinish.resumeAt 175)
      (requestSteps + 1 + extra) =
      PMF.pure (prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding) := by
    rw [evalConfigWithin_add, hCall, PMF.pure_bind]
    induction extra with
    | zero => rfl
    | succ extra ih =>
        rw [evalConfigWithin, ih, PMF.pure_bind]
        have hStopped : (prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding).halted = true := rfl
        simp [stepPMF, next, hStopped]
  have hAfter := evalConfigWithin_after_return prepareGuessInput 175
    (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
    bodySteps (requestSteps + 1) id (by
      intro d hd _hPc extra
      rw [hRaw] at hd
      have heq : d = bodyFinish.resumeAt 175 := by simpa using hd
      subst d
      rw [hTail extra, hTail 0])
  simp only [PMF.map_id] at hAfter
  change evalConfigWithin prepareGuessInput
    (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
    (bodySteps + (requestSteps + 1)) = _
  rw [hAfter, hRaw, PMF.pure_bind, hCall]

theorem prepareGuessInputFinish_output (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (padding : Nat) :
    (prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits ++
          frame (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product))).reverse.map some ++
          none :: none :: (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)).reverse.map some ++ none :: beforeOutput } :=
  prepareGuessRequestFinish_output before beforeOutput n instanceBits (guessInputTupleTail first second last)
    reply (canonicalMessageBits message₀ message₁ state) selected product
    (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)) padding

theorem prepareGuessInput_length : prepareGuessInput.length = 360 := by
  simp [prepareGuessInput, Program.asSubroutine_length, prepareGuessBody_length, prepareGuessRequest_length]

theorem prepareGuessInput_steps_le (n : Nat)
    (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    prepareGuessInputSteps n instanceBits first second last reply message₀ message₁ state selected product ≤
      250*(n + instanceBits.length + first.length + second.length + last.length + reply.length +
        message₀.length + message₁.length + state.length + selected.length + product.length + 1) + 800 := by
  have hb := prepareGuessBody_steps_le n instanceBits first second last reply message₀ message₁ state selected product
  have hr := prepareGuessRequest_steps_le n instanceBits (guessInputTupleTail first second last)
    reply (canonicalMessageBits message₀ message₁ state) selected product
    (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product))
  simp only [prepareGuessInputSteps]
  simp only [guessInputTupleTail, guessInputTuple, canonicalMessageBits,
    encodeSecurityParameter, frame, List.length_append, List.length_cons,
    List.length_replicate, List.length_nil, FiniteBitEncoding.delimit_length] at hr ⊢
  omega

theorem prepareGuessInput_haltsFrom (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (padding : Nat) (finish : Configuration)
    (run : PaddedRunsFor prepareGuessInput
      (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
      finish (prepareGuessInputSteps n instanceBits first second last reply message₀ message₁ state selected product)) :
    finish.halted = true := by
  have hm := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [prepareGuessInput_eval] at hm
  have heq : finish = prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding := by simpa using hm
  rw [heq]
  rfl

/-- Start the complete guess-input constructor from the actual guarded
multiplication return. Its product is the returned source output; source
scratch and caller data are retained in the same finite configuration. -/
theorem returnedFrameResult_guessInput_layout (source : Program) (request : List Bool)
    (beforeInput before : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected : List Bool)
    (c : Configuration) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++
      frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)
    let saved := selected.reverse.map some ++ none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
      none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let returned := GuardedCompiler.returnedFrameResult source request beforeInput saved c
    returned.resumeAt 0 = prepareGuessInputStart before returned.outputTape.left
      n instanceBits first second last reply message₀ message₁ state selected c.outputBits
      (2*c.outputTape.cells + 2 - c.outputBits.length) := by
  dsimp only
  exact returnedFrameResult_guessBody_layout source request beforeInput before n instanceBits first second last reply message₀ message₁ state selected c

theorem prepareGuessInput_returnedFrameResult_eval (source : Program) (request : List Bool)
    (beforeInput before : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected : List Bool)
    (c : Configuration) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++
      frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)
    let saved := selected.reverse.map some ++ none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
      none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let returned := GuardedCompiler.returnedFrameResult source request beforeInput saved c
    evalConfigWithin prepareGuessInput (returned.resumeAt 0)
      (prepareGuessInputSteps n instanceBits first second last reply message₀ message₁ state selected c.outputBits) =
      PMF.pure (prepareGuessInputFinish before returned.outputTape.left
        n instanceBits first second last reply message₀ message₁ state selected c.outputBits
        (2*c.outputTape.cells + 2 - c.outputBits.length)) := by
  dsimp only
  rw [returnedFrameResult_guessInput_layout]
  exact prepareGuessInput_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Full native return law for placement in the final simulator. Code and
return addresses depend only on finite syntax, not on security parameters,
source states, messages, or products. -/
theorem prepareGuessInput_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ prepareGuessInput.length → pre.length + pc ≠ returnPc)
    (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (padding : Nat) :
    evalReturnWithin (Program.withSubroutine pre prepareGuessInput suffix returnPc) returnPc
      ((prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding).rebasePc pre.length)
      (prepareGuessInputSteps n instanceBits first second last reply message₀ message₁ state selected product) =
      PMF.pure ((prepareGuessInputFinish before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding).resumeAt returnPc) := by
  rw [Program.evalReturnWithin_configuration_eq_of_halted pre prepareGuessInput suffix returnPc hLayout
      (prepareGuessInputStart before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding)
      (by change 0 ≤ prepareGuessInput.length; exact Nat.zero_le _) rfl
      (prepareGuessInputSteps n instanceBits first second last reply message₀ message₁ state selected product)
      (prepareGuessInput_haltsFrom before beforeOutput n instanceBits first second last reply message₀ message₁ state selected product padding),
    prepareGuessInput_eval, PMF.pure_map]

end Machine
