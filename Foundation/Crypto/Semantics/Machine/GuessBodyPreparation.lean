import Foundation.Crypto.Semantics.Machine.GuessCiphertextPreparation

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


/-- The complete native guess-body preparation stops on arbitrary finite
caller tapes. This includes malformed retained choose/DDH/product data.
The coarse linear bound charges growth of the actual intermediate storage;
no source response is supplied again through a fresh initial configuration. -/
private theorem prepareGuessBody_terminates_core (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000000000000000000 * (input.cells + output.cells) + 1000000000000000000000000000 ∧
      RunsFor prepareGuessBody
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      (∀ before blanks, output = { left := before, right := List.replicate blanks none } →
        ∃ after remaining,
          finish.outputTape = { left := after, right := List.replicate remaining none }) := by
  obtain ⟨stateReady, stateTime, hStateTime, stateRun, stateHalt⟩ :=
    prepareGuessStateBody_terminates_from_anyTape input output
  obtain ⟨ciphertextReady, ciphertextTime, hCiphertextTime, ciphertextRun, ciphertextHalt⟩ :=
    prepareGuessCiphertextFirst_terminates_from_anyTape stateReady.inputTape stateReady.outputTape
  obtain ⟨productReady, productTime, hProductTime, productRun, productHalt⟩ :=
    appendStoredGuessProduct_terminates_from_anyTape ciphertextReady.inputTape ciphertextReady.outputTape
  have hState := stateRun.withSubroutine_halted_of_closed
    [] prepareGuessStateBody (prepareGuessCiphertextFirst.asSubroutine 62 138 ++
      appendStoredGuessProduct.asSubroutine 138 173 ++ [.halt]) 62
    (by change 0 < 61; decide) rfl stateHalt prepareGuessStateBody_control_closed
  change RunsFor prepareGuessBody
    ({ inputTape := input, outputTape := output } : Configuration) (stateReady.resumeAt 62) stateTime at hState
  have hCiphertext := ciphertextRun.withSubroutine_halted_of_closed
    (prepareGuessStateBody.asSubroutine 0 62) prepareGuessCiphertextFirst
    (appendStoredGuessProduct.asSubroutine 138 173 ++ [.halt]) 138
    (by change 0 < 75; decide) rfl ciphertextHalt prepareGuessCiphertextFirst_control_closed
  change RunsFor prepareGuessBody (stateReady.resumeAt 62) (ciphertextReady.resumeAt 138) ciphertextTime at hCiphertext
  have toProduct := hState.trans hCiphertext
  have hProduct := productRun.withSubroutine_halted_of_closed
    (prepareGuessStateBody.asSubroutine 0 62 ++ prepareGuessCiphertextFirst.asSubroutine 62 138)
    appendStoredGuessProduct [.halt] 173
    (by change 0 < 34; decide) rfl productHalt appendStoredGuessProduct_control_closed
  change RunsFor prepareGuessBody (ciphertextReady.resumeAt 138) (productReady.resumeAt 173) productTime at hProduct
  let finish : Configuration := { productReady with pc := 173, halted := true }
  have last : Step prepareGuessBody (productReady.resumeAt 173) finish := by
    have code : prepareGuessBody[173]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, stateTime + ciphertextTime + productTime + 1, ?_, RunsFor.succ (toProduct.trans hProduct) last, rfl, ?_⟩
  · have stateStorage := GuardedCompiler.sourceStorage_le_of_run stateRun
    change stateReady.inputTape.cells + stateReady.outputTape.cells ≤ input.cells + output.cells + stateTime at stateStorage
    have ciphertextStorage := GuardedCompiler.sourceStorage_le_of_run toProduct
    change ciphertextReady.inputTape.cells + ciphertextReady.outputTape.cells ≤ input.cells + output.cells + (stateTime + ciphertextTime) at ciphertextStorage
    omega
  · intro before blanks hOutput
    obtain ⟨stateFresh, stateFreshTime, stateAfter, stateBlanks, _hStateFreshTime,
      stateFreshRun, stateFreshHalt, stateLayout⟩ :=
      prepareGuessStateBody_terminates_with_output_layout input before blanks
    rw [hOutput] at stateRun
    have hStateEq := stateRun.halted_finish_eq_of_no_randomBit stateFreshRun
      stateHalt stateFreshHalt prepareGuessStateBody_no_randomBit
    have hStateOutput : stateReady.outputTape =
        { left := stateAfter, right := List.replicate stateBlanks none } := by
      rw [hStateEq]
      exact stateLayout
    obtain ⟨ciphertextFresh, ciphertextFreshTime, ciphertextAfter, ciphertextBlanks,
      _hCiphertextFreshTime, ciphertextFreshRun, ciphertextFreshHalt, ciphertextLayout⟩ :=
      prepareGuessCiphertextFirst_terminates_with_output_layout stateReady.inputTape stateAfter stateBlanks
    rw [hStateOutput] at ciphertextRun
    have hCiphertextEq := ciphertextRun.halted_finish_eq_of_no_randomBit ciphertextFreshRun
      ciphertextHalt ciphertextFreshHalt prepareGuessCiphertextFirst_no_randomBit
    have hCiphertextOutput : ciphertextReady.outputTape =
        { left := ciphertextAfter, right := List.replicate ciphertextBlanks none } := by
      rw [hCiphertextEq]
      exact ciphertextLayout
    obtain ⟨productFresh, productFreshTime, productAfter, productBlanks,
      _hProductFreshTime, productFreshRun, productFreshHalt, productLayout⟩ :=
      appendStoredGuessProduct_terminates_with_output_layout ciphertextReady.inputTape ciphertextAfter ciphertextBlanks
    rw [hCiphertextOutput] at productRun
    have hProductEq := productRun.halted_finish_eq_of_no_randomBit productFreshRun
      productHalt productFreshHalt appendStoredGuessProduct_no_randomBit
    refine ⟨productAfter, productBlanks, ?_⟩
    change productReady.outputTape = _
    rw [hProductEq]
    exact productLayout

theorem prepareGuessBody_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000000000000000000 * (input.cells + output.cells) + 1000000000000000000000000000 ∧
      RunsFor prepareGuessBody
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hLayout⟩ := prepareGuessBody_terminates_core input output
  exact ⟨finish, used, hBound, run, hHalted⟩

/-- State serialization, ciphertext copying and product copying preserve the
fresh output frontier along the same actual native execution. Malformed
retained data are allowed; no intermediate tape is reset or reconstructed. -/
theorem prepareGuessBody_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 1000000000000000000000000000 * (input.cells +
        ({ left := before, right := List.replicate blanks none } : Tape).cells) + 1000000000000000000000000000 ∧
      RunsFor prepareGuessBody
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hLayout⟩ :=
    prepareGuessBody_terminates_core input { left := before, right := List.replicate blanks none }
  obtain ⟨after, remaining, hOutput⟩ := hLayout before blanks rfl
  exact ⟨finish, used, after, remaining, hBound, run, hHalted, hOutput⟩

theorem prepareGuessBody_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareGuessBody
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000000000000000000000000 * (input.cells + output.cells) + 1000000000000000000000000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ := prepareGuessBody_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted prepareGuessBody_no_randomBit hBound finish trace

/-- Actual retained raw request/reply/normalizer/selection/product blocks
suffice for both fresh return tapes. In particular the normalizer block
need not be a valid canonical response. The source position is tracked
through state reading, three-block restoration and native field copying;
no earlier caller data are reloaded or supplied as parsed values. -/
theorem prepareGuessBody_terminates_with_retained_frontiers
    (before beforeOutput : List (Option Bool))
    (original reply canonical selected product : List Bool) (inputBlanks outputBlanks : Nat) :
    let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
    let start := restoreStoredInputStart
      (reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before)
      canonical selected product none (List.replicate inputBlanks none) output
    ∃ finish used afterInput remainingInput afterOutput remainingOutput,
      used ≤ 1000000000000000000000000000 * (start.inputTape.cells + output.cells) +
        1000000000000000000000000000 ∧
      RunsFor prepareGuessBody start finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate remainingInput none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remainingOutput none } := by
  dsimp only
  let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
  let beforeCanonical := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
  let start := restoreStoredInputStart beforeCanonical canonical selected product none
    (List.replicate inputBlanks none) output
  let base := (restoreStoredInputFinish beforeCanonical canonical selected product none
    (List.replicate inputBlanks none) output).inputTape
  let retained := none :: reply.reverse.map some ++ none :: original.reverse.map some
  have hBase : ({ left := retained ++ none :: before, current := base.current, right := base.right } : Tape) = base := by
    cases canonical <;> simp [base, restoreStoredInputFinish, retained, beforeCanonical,
      Tape.moveRight, List.append_assoc]
  have hSeparators : 2 ≤ retained.count none := by
    simp only [retained, List.count_append, List.count_cons_self]
    omega
  obtain ⟨stateReady, stateTime, stateMoves, stateAfter, stateBlanks, hStateTime,
    stateRun, stateHalt, stateOutput, _hStateMoves, stateInput⟩ :=
    prepareGuessStateBody_terminates_with_retained_input beforeCanonical canonical selected product none
      (List.replicate inputBlanks none) beforeOutput outputBlanks
  change stateReady.inputTape = (Tape.moveRight^[stateMoves]) base at stateInput
  obtain ⟨ciphertextReady, ciphertextTime, ciphertextAfter, ciphertextBlanks,
    count, padding, hCiphertextTime, ciphertextRun, ciphertextHalt, ciphertextOutput, ciphertextStream⟩ :=
    prepareGuessCiphertextFirst_terminates_after_input_moves retained before base.current base.right
      stateAfter stateBlanks stateMoves hSeparators
  have hCiphertextEntry : (Tape.moveRight^[stateMoves])
      ({ left := retained ++ none :: before, current := base.current, right := base.right } : Tape) =
      stateReady.inputTape := by rw [hBase, ← stateInput]
  rw [hCiphertextEntry] at ciphertextRun hCiphertextTime
  have hRoot : retained.reverse ++ base.current :: base.right ++ List.replicate padding none =
      original.map some ++ none :: reply.map some ++ none :: canonical.map some ++
        none :: selected.map some ++ none :: product.map some ++ none ::
          List.replicate (inputBlanks + padding) none := by
    cases canonical <;> simp [retained, base, restoreStoredInputFinish, beforeCanonical,
      Tape.moveRight, List.reverse_append, List.reverse_cons, List.map_reverse,
      List.append_assoc]
  rw [hRoot] at ciphertextStream
  obtain ⟨productReady, productTime, afterInput, remainingInput, afterOutput, remainingOutput,
    hProductTime, productRun, productHalt, productInput, productOutput⟩ :=
    appendStoredGuessProduct_terminates_with_stream_frontier ciphertextReady.inputTape
      ciphertextAfter ciphertextBlanks original reply canonical selected product
      (inputBlanks + padding) count ciphertextStream
  have actualCiphertext : RunsFor prepareGuessCiphertextFirst
      ({ inputTape := stateReady.inputTape, outputTape := stateReady.outputTape } : Configuration)
      ciphertextReady ciphertextTime := by
    rw [stateOutput]
    exact ciphertextRun
  have actualProduct : RunsFor appendStoredGuessProduct
      ({ inputTape := ciphertextReady.inputTape, outputTape := ciphertextReady.outputTape } : Configuration)
      productReady productTime := by
    rw [ciphertextOutput]
    exact productRun
  have hState := stateRun.withSubroutine_halted_of_closed
    [] prepareGuessStateBody (prepareGuessCiphertextFirst.asSubroutine 62 138 ++
      appendStoredGuessProduct.asSubroutine 138 173 ++ [.halt]) 62
    (by change 0 < 61; decide) rfl stateHalt prepareGuessStateBody_control_closed
  change RunsFor prepareGuessBody start (stateReady.resumeAt 62) stateTime at hState
  have hCiphertext := actualCiphertext.withSubroutine_halted_of_closed
    (prepareGuessStateBody.asSubroutine 0 62) prepareGuessCiphertextFirst
    (appendStoredGuessProduct.asSubroutine 138 173 ++ [.halt]) 138
    (by change 0 < 75; decide) rfl ciphertextHalt prepareGuessCiphertextFirst_control_closed
  change RunsFor prepareGuessBody (stateReady.resumeAt 62) (ciphertextReady.resumeAt 138) ciphertextTime at hCiphertext
  have toProduct := hState.trans hCiphertext
  have hProduct := actualProduct.withSubroutine_halted_of_closed
    (prepareGuessStateBody.asSubroutine 0 62 ++ prepareGuessCiphertextFirst.asSubroutine 62 138)
    appendStoredGuessProduct [.halt] 173
    (by change 0 < 34; decide) rfl productHalt appendStoredGuessProduct_control_closed
  change RunsFor prepareGuessBody (ciphertextReady.resumeAt 138) (productReady.resumeAt 173) productTime at hProduct
  let finish : Configuration := { productReady with pc := 173, halted := true }
  have last : Step prepareGuessBody (productReady.resumeAt 173) finish := by
    have code : prepareGuessBody[173]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, stateTime + ciphertextTime + productTime + 1,
    afterInput, remainingInput, afterOutput, remainingOutput, ?_,
    RunsFor.succ (toProduct.trans hProduct) last, rfl, productInput, productOutput⟩
  have stateStorage := GuardedCompiler.sourceStorage_le_of_run stateRun
  change stateReady.inputTape.cells + stateReady.outputTape.cells ≤
    start.inputTape.cells + output.cells + stateTime at stateStorage
  have ciphertextStorage := GuardedCompiler.sourceStorage_le_of_run toProduct
  change ciphertextReady.inputTape.cells + ciphertextReady.outputTape.cells ≤
    start.inputTape.cells + output.cells + (stateTime + ciphertextTime) at ciphertextStorage
  change stateTime ≤ 1000000000 * (start.inputTape.cells + output.cells) + 1000000000 at hStateTime
  rw [← stateOutput] at hCiphertextTime
  rw [← ciphertextOutput] at hProductTime
  change stateTime + ciphertextTime + productTime + 1 ≤
    1000000000000000000000000000 * (start.inputTape.cells + output.cells) + 1000000000000000000000000000
  omega

end Machine
