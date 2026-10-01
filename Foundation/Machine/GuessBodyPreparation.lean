import Foundation.Machine.GuessCiphertextPreparation

namespace Machine

/-- Complete raw guess-body construction after multiplication: restore and
serialize the retained state, restore and copy the DDH ciphertext component,
and scan to the retained product and copy it. All 174 instructions are fixed
native instructions, independent of the security parameter and source state.
The public request prefix and outer framing remain a subsequent stage. -/
def prepareGuessBody : Program :=
  prepareGuessStateBody.asSubroutine 0 62 ++
    prepareGuessCiphertextFirst.asSubroutine 62 138 ++
    appendStoredGuessProduct.asSubroutine 138 173 ++ [.halt]

private def originalDDH (n : Nat) (instanceBits first second last : List Bool) : List Bool :=
  encodeSecurityParameter n ++ frame instanceBits ++
    frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)

private def beforeDDHLast (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last : List Bool) : List (Option Bool) :=
  (FiniteBitEncoding.delimit second).reverse.map some ++ (FiniteBitEncoding.delimit first).reverse.map some ++
    (encodeSecurityParameter (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length).reverse.map some ++
    (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: before

private def guessBodyBeforeProduct (beforeOutput : List (Option Bool))
    (state second : List Bool) : List (Option Bool) :=
  (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second)).reverse.map some ++ none :: beforeOutput

def prepareGuessBodyStart (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) : Configuration :=
  prepareGuessStateBodyStart
    (reply.reverse.map some ++ none :: (originalDDH n instanceBits first second last).reverse.map some ++ none :: before)
    padding beforeOutput message₀ message₁ state selected product 0

def prepareGuessBodyFinish (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) : Configuration :=
  { appendStoredGuessProductFinish (beforeDDHLast before n instanceBits first second last)
      (guessBodyBeforeProduct beforeOutput state second) padding last reply
      (canonicalMessageBits message₀ message₁ state) selected product
      (instanceBits.length + 1 - (2*second.length + 1)) with pc := 173 }

def prepareGuessBodySteps
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) : Nat :=
  prepareGuessStateBodySteps message₀ message₁ state selected product +
    prepareGuessCiphertextFirstSteps n instanceBits first second last reply message₀ message₁ state +
    appendStoredGuessProductSteps last reply (canonicalMessageBits message₀ message₁ state) selected product + 1

theorem prepareGuessBody_runs (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    RunsFor prepareGuessBody
      (prepareGuessBodyStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
      (prepareGuessBodyFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
      (prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected product) := by
  let beforeCanonical := reply.reverse.map some ++ none :: (originalDDH n instanceBits first second last).reverse.map some ++ none :: before
  let stateFinish := prepareGuessStateBodyFinish beforeCanonical padding beforeOutput message₀ message₁ state selected product 0
  let firstStart := prepareGuessCiphertextFirstStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product
  let firstFinish := prepareGuessCiphertextFirstFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product
  let productStart := appendStoredGuessProductStart (beforeDDHLast before n instanceBits first second last)
    (guessBodyBeforeProduct beforeOutput state second) padding last reply (canonicalMessageBits message₀ message₁ state) selected product
    (instanceBits.length + 1 - (2*second.length + 1))
  have hState := (prepareGuessStateBody_runs beforeCanonical padding beforeOutput message₀ message₁ state selected product 0).withSubroutine_halted_of_closed
    [] prepareGuessStateBody (prepareGuessCiphertextFirst.asSubroutine 62 138 ++
      appendStoredGuessProduct.asSubroutine 138 173 ++ [.halt]) 62
    (by change 0 < 61; decide) rfl rfl prepareGuessStateBody_control_closed
  change RunsFor prepareGuessBody
    (prepareGuessBodyStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
    (stateFinish.resumeAt 62) (prepareGuessStateBodySteps message₀ message₁ state selected product) at hState
  have hFirstStart : stateFinish.resumeAt 62 = firstStart.rebasePc 62 := by
    change stateFinish.resumeAt 62 = (restoreStoredInputStart before
      (originalDDH n instanceBits first second last) reply (canonicalMessageBits message₀ message₁ state)
      none (selected.map some ++ none :: product.map some ++ none :: padding)
      { left := (true :: FiniteBitEncoding.delimit state).reverse.map some ++ none :: beforeOutput }).rebasePc 62
    simp [stateFinish, beforeCanonical, prepareGuessStateBodyFinish, serializeGuessStateFinish,
      writeDelimitedContextFinish, restoreStoredInputStart, canonicalMessageBits,
      Configuration.resumeAt, Configuration.rebasePc, List.reverse_cons, List.reverse_append,
      List.map_append, List.append_assoc]
  rw [hFirstStart] at hState
  have hFirst := (prepareGuessCiphertextFirst_runs before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).withSubroutine_halted_of_closed
    (prepareGuessStateBody.asSubroutine 0 62) prepareGuessCiphertextFirst
    (appendStoredGuessProduct.asSubroutine 138 173 ++ [.halt]) 138
    (by change 0 < 75; decide) rfl rfl prepareGuessCiphertextFirst_control_closed
  change RunsFor prepareGuessBody (firstStart.rebasePc 62) (firstFinish.resumeAt 138)
    (prepareGuessCiphertextFirstSteps n instanceBits first second last reply message₀ message₁ state) at hFirst
  have hProductStart : firstFinish.resumeAt 138 = productStart.rebasePc 138 := by
    have h := prepareGuessCiphertextFirstFinish_product_layout before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product
    simpa [firstFinish, productStart, beforeDDHLast, guessBodyBeforeProduct,
      appendStoredGuessProductStart, seekBitstringNextStart_layout,
      Configuration.resumeAt, Configuration.rebasePc, List.append_assoc] using
      congrArg (fun c : Configuration => c.rebasePc 138) h
  rw [hProductStart] at hFirst
  have hProduct := (appendStoredGuessProduct_runs (beforeDDHLast before n instanceBits first second last)
    (guessBodyBeforeProduct beforeOutput state second) padding last reply (canonicalMessageBits message₀ message₁ state) selected product
    (instanceBits.length + 1 - (2*second.length + 1))).withSubroutine_halted_of_closed
    (prepareGuessStateBody.asSubroutine 0 62 ++ prepareGuessCiphertextFirst.asSubroutine 62 138)
    appendStoredGuessProduct [.halt] 173 (by change 0 < 34; decide) rfl rfl appendStoredGuessProduct_control_closed
  change RunsFor prepareGuessBody (productStart.rebasePc 138)
    ((prepareGuessBodyFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).resumeAt 173)
    (appendStoredGuessProductSteps last reply (canonicalMessageBits message₀ message₁ state) selected product) at hProduct
  have hPrefixLength : (prepareGuessStateBody.asSubroutine 0 62 ++
      prepareGuessCiphertextFirst.asSubroutine 62 138 ++ appendStoredGuessProduct.asSubroutine 138 173).length = 173 := by
    simp only [List.length_append, Program.asSubroutine_length,
      show prepareGuessStateBody.length = 61 from rfl,
      show prepareGuessCiphertextFirst.length = 75 from rfl,
      show appendStoredGuessProduct.length = 34 from rfl]
  have hInstruction : prepareGuessBody[173]? = some Instruction.halt := by
    change (prepareGuessStateBody.asSubroutine 0 62 ++
      prepareGuessCiphertextFirst.asSubroutine 62 138 ++ appendStoredGuessProduct.asSubroutine 138 173 ++ [.halt])[173]? = _
    rw [List.getElem?_append_right (by rw [hPrefixLength]), hPrefixLength]
    rfl
  have hHalt : Step prepareGuessBody
      ((prepareGuessBodyFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).resumeAt 173)
      (prepareGuessBodyFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product) := by
    simp [Step, successors, next, prepareGuessBodyFinish, appendStoredGuessProductFinish,
      copySegmentFinish, Configuration.resumeAt, hInstruction, Instruction.next]
  exact RunsFor.succ ((hState.trans hFirst).trans hProduct) hHalt

private theorem nativeSubroutine_no_randomBit (source : Program) (base returnPc : Nat)
    (h : ∀ tape, Instruction.randomBit tape ∉ source) (tape : TapeId) :
    Instruction.randomBit tape ∉ source.asSubroutine base returnPc := by
  intro hm
  simp only [Program.asSubroutine, List.mem_append, List.mem_map, List.mem_singleton] at hm
  rcases hm with ⟨i, hi, heq⟩ | heq
  · have hOriginal : i = Instruction.randomBit tape := by
      cases i <;> simp_all [Instruction.asSubroutine]
    exact h tape (hOriginal ▸ hi)
  · cases heq

theorem prepareGuessBody_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareGuessBody := by
  simp only [prepareGuessBody, List.mem_append, List.mem_singleton, not_or]
  exact ⟨⟨⟨nativeSubroutine_no_randomBit _ _ _ prepareGuessStateBody_no_randomBit tape,
    nativeSubroutine_no_randomBit _ _ _ prepareGuessCiphertextFirst_no_randomBit tape⟩,
    nativeSubroutine_no_randomBit _ _ _ appendStoredGuessProduct_no_randomBit tape⟩, by simp⟩

theorem prepareGuessBody_eval (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    evalConfigWithin prepareGuessBody
      (prepareGuessBodyStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
      (prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected product) =
      PMF.pure (prepareGuessBodyFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product) :=
  (prepareGuessBody_runs _ _ _ _ _ _ _ _ _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit prepareGuessBody_no_randomBit

theorem prepareGuessBodyFinish_output (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    (prepareGuessBodyFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).outputTape =
      { left := (true :: (FiniteBitEncoding.delimit state ++ FiniteBitEncoding.delimit second ++ product)).reverse.map some ++ none :: beforeOutput,
        right := List.replicate (instanceBits.length + 1 - (2*second.length + 1) - product.length) none } :=
  appendStoredGuessProductFinish_guessBody_output (beforeDDHLast before n instanceBits first second last)
    beforeOutput padding last reply message₀ message₁ state selected second product
    (instanceBits.length + 1 - (2*second.length + 1))

/-- Physical retained input blocks at the raw-body return. The returned
product is the same contiguous block read by the following request stage. -/
theorem prepareGuessBodyFinish_input (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    (prepareGuessBodyFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).inputTape =
      { left := product.reverse.map some ++ none :: selected.reverse.map some ++
          none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
          none :: reply.reverse.map some ++ none ::
          (encodeSecurityParameter n ++ frame instanceBits ++
            frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)).reverse.map some ++ none :: before
        right := padding } := by
  simp [prepareGuessBodyFinish, appendStoredGuessProductFinish, copySegmentFinish,
    beforeDDHLast, frame, encodeSecurityParameter, List.reverse_append,
    List.map_append, List.append_assoc]

theorem prepareGuessBody_length : prepareGuessBody.length = 174 := by
  simp only [prepareGuessBody, List.length_append, List.length_singleton, Program.asSubroutine_length,
    show prepareGuessStateBody.length = 61 from rfl,
    show prepareGuessCiphertextFirst.length = 75 from rfl,
    show appendStoredGuessProduct.length = 34 from rfl]

theorem prepareGuessBody_steps_le
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected product ≤
      5*n + 14*instanceBits.length + 18*first.length + 24*second.length + 10*last.length +
        5*reply.length + 18*(message₀.length + message₁.length) + 15*state.length +
        5*selected.length + 8*product.length + 127 := by
  have hs := prepareGuessStateBody_steps_le message₀ message₁ state selected product
  have hc := prepareGuessCiphertextFirst_steps_le n instanceBits first second last reply message₀ message₁ state
  have hp := appendStoredGuessProduct_steps_le last reply (canonicalMessageBits message₀ message₁ state) selected product
  simp only [canonicalMessageBits, List.length_cons, List.length_append, FiniteBitEncoding.delimit_length] at hp
  simp only [prepareGuessBodySteps, canonicalMessageBits]
  omega

/-- The actual guarded multiplication return and framing supplies this
continuation's exact entry. The product is the source machine's real output;
all its virtual scratch, the selected message, canonical response and
original DDH input remain in the finite configuration. -/
theorem returnedFrameResult_guessBody_layout (source : Program) (request : List Bool)
    (beforeInput before : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected : List Bool)
    (c : Configuration) :
    let saved := selected.reverse.map some ++ none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
      none :: reply.reverse.map some ++ none :: (originalDDH n instanceBits first second last).reverse.map some ++ none :: before
    let returned := GuardedCompiler.returnedFrameResult source request beforeInput saved c
    returned.resumeAt 0 = prepareGuessBodyStart before
      (List.replicate (2*c.outputTape.cells + 2 - c.outputBits.length) none) returned.outputTape.left
      n instanceBits first second last reply message₀ message₁ state selected c.outputBits := by
  dsimp only
  simp [GuardedCompiler.returnedFrameResult, frameReturnedResultFinish,
    prepareGuessBodyStart, prepareGuessStateBodyStart, prepareGuessStateStart,
    restoreStoredInputStart, Configuration.resumeAt, List.append_assoc]

theorem prepareGuessBody_returnedFrameResult_eval (source : Program) (request : List Bool)
    (beforeInput before : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected : List Bool)
    (c : Configuration) :
    let saved := selected.reverse.map some ++ none :: (canonicalMessageBits message₀ message₁ state).reverse.map some ++
      none :: reply.reverse.map some ++ none :: (originalDDH n instanceBits first second last).reverse.map some ++ none :: before
    let returned := GuardedCompiler.returnedFrameResult source request beforeInput saved c
    evalConfigWithin prepareGuessBody (returned.resumeAt 0)
      (prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected c.outputBits) =
      PMF.pure (prepareGuessBodyFinish before
        (List.replicate (2*c.outputTape.cells + 2 - c.outputBits.length) none) returned.outputTape.left
        n instanceBits first second last reply message₀ message₁ state selected c.outputBits) := by
  dsimp only
  rw [returnedFrameResult_guessBody_layout]
  exact prepareGuessBody_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem prepareGuessBody_haltsFrom (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool)
    (finish : Configuration)
    (run : PaddedRunsFor prepareGuessBody
      (prepareGuessBodyStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
      finish (prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected product)) :
    finish.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [prepareGuessBody_eval] at hMem
  have hEq : finish = prepareGuessBodyFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product := by
    simpa using hMem
  rw [hEq]
  rfl

/-- Exact full-configuration return law when this finite continuation is
embedded in arbitrary caller code. The return location lies outside the
callee's local addresses; no caller transition or virtual reset is free. -/
theorem prepareGuessBody_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ prepareGuessBody.length → pre.length + pc ≠ returnPc)
    (before padding beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    evalReturnWithin (Program.withSubroutine pre prepareGuessBody suffix returnPc) returnPc
      ((prepareGuessBodyStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).rebasePc pre.length)
      (prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected product) =
      PMF.pure ((prepareGuessBodyFinish before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product).resumeAt returnPc) := by
  rw [Program.evalReturnWithin_configuration_eq_of_halted pre prepareGuessBody suffix returnPc hLayout
      (prepareGuessBodyStart before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product)
      (by change 0 ≤ prepareGuessBody.length; exact Nat.zero_le _) rfl (prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected product)
      (prepareGuessBody_haltsFrom before padding beforeOutput n instanceBits first second last reply message₀ message₁ state selected product),
    prepareGuessBody_eval, PMF.pure_map]

end Machine
