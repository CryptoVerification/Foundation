import Foundation.Crypto.Semantics.Machine.NativeFixedRawTransfer
import Foundation.Crypto.Semantics.Machine.NativeKeyPairOutputPacket

/-! One closed native program prepares a delimited request, then continues
through cipher generation, history erasure, ciphertext toggling and key testing.
Request bits are physically transferred back to the input tape before the
original callee runs. The final decision remains on the original output tape. -/
namespace Machine.NativePreparedKeyDecision
open Foundation.Probability NativeUniformSequence NativeBitDecisionTree NativeBoundedFlaggedTransfer
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal

attribute [local irreducible] NativeControlledEightBitCipher.code

def request (v : OrderedGridVertex 32) (message : Bool) : List Bool :=
  List.ofFn (EightBitCipherControl.request v message)

theorem request_length (v : OrderedGridVertex 32) (message : Bool) : (request v message).length = 19 :=
  by simp only [request, List.length_ofFn]

def rawInput (v : OrderedGridVertex 32) (message : Bool) : List Bool :=
  FiniteBitEncoding.delimit (request v message)

theorem rawInput_length (v : OrderedGridVertex 32) (message : Bool) : (rawInput v message).length = 39 := by
  rw [rawInput, FiniteBitEncoding.delimit_length, request_length]

def firstPreparation : Program := NativeFlaggedRequestPreparation.code 19

def preparation : Program := firstPreparation.followedBy (NativeFixedRawTransfer.restoredCode 19)

def source : Program := NativeKeyPairDecisionExecution.code

def code : Program := preparation.followedBy source

def entry (v : OrderedGridVertex 32) (message : Bool) : Configuration :=
  NativeBitChoice.start (preload (rawInput v message) (NativeBitGenerator.blankBlock 19 {})) (NativeBitGenerator.blankBlock 19 {})

def prepared (v : OrderedGridVertex 32) (message : Bool) : Configuration :=
  {pc := 723, inputTape := preload (request v message) (erasedBefore 39 {}), outputTape := erasedBefore 19 {}, halted := true}

def readDecision (c : Configuration) : Option Bool := NativeKeyPairDecisionExecution.readDecision c

theorem readDecision_control (c : Configuration) (pc : ℕ) :
    readDecision {c with pc := pc, halted := true} = readDecision c := rfl

theorem readDecision_equivalent (c d : Configuration) (h : c.Equivalent d) :
    readDecision c = readDecision d := h.2.2.2.2.1 0

theorem preparation_stops : StopsEverywhere preparation 487 :=
  NativeUniformSequence.stops firstPreparation (NativeFixedRawTransfer.restoredCode 19) 274 212
    (NativeFlaggedRequestPreparation.stops 19) (NativeFixedRawTransfer.restored_stops 19)

theorem preparation_length : preparation.length = 724 := by
  unfold preparation firstPreparation
  rw [NativeUniformSequence.code_length, NativeFlaggedRequestPreparation.code_length,
    NativeFixedRawTransfer.restored_length]

theorem source_stops : StopsEverywhere source 442 := NativeKeyPairDecisionExecution.stops

theorem stops : StopsEverywhere code 930 :=
  NativeUniformSequence.stops preparation source 487 442 preparation_stops source_stops

theorem blankBlock_erasedBefore (n m : ℕ) (suffix : Tape) :
    NativeBitGenerator.blankBlock n (erasedBefore m suffix) =
      erasedBefore m (NativeBitGenerator.blankBlock n suffix) := by
  cases n <;> rfl

theorem preparation_run (v : OrderedGridVertex 32) (message : Bool) :
    evalConfigWithin preparation (entry v message) 487 = PMF.pure (prepared v message) := by
  have hFirst := NativeFlaggedRequestPreparation.run (request v message)
    (NativeBitGenerator.blankBlock 19 {}) {}
  simp only [request_length] at hFirst
  change evalConfigWithin firstPreparation (entry v message) 274 = _ at hFirst
  have hBack := NativeFixedRawTransfer.restored_run (request v message) (erasedBefore 39 {}) {}
  simp only [request_length] at hBack
  unfold preparation entry
  rw [show 487 = 274 + 212 + 1 from rfl,
    NativeUniformSequence.run firstPreparation (NativeFixedRawTransfer.restoredCode 19) 274 212
      (NativeFlaggedRequestPreparation.stops 19) (NativeFixedRawTransfer.restored_stops 19)]
  change (evalConfigWithin firstPreparation (entry v message) 274).bind _ = _
  rw [hFirst, PMF.pure_bind]
  change (evalConfigWithin (NativeFixedRawTransfer.restoredCode 19)
    (NativeBitChoice.start (erasedBefore 39 (NativeBitGenerator.blankBlock 19 {}))
      (preload (request v message) {})) 212).map _ = _
  rw [← blankBlock_erasedBefore, hBack, PMF.pure_map]
  apply congrArg PMF.pure
  simp [firstPreparation, prepared, NativeFixedRawTransfer.restoredFinish, request_length,
    NativeFlaggedRequestPreparation.code_length, NativeFixedRawTransfer.restored_length]

theorem erasedBefore_blank (n : ℕ) : (erasedBefore n {}).Equivalent ({} : Tape) := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro i
  change (List.replicate n (none : Option Bool) ++ []).getD i none = none
  rw [List.append_nil]
  simpa only [List.getD_eq_getElem?_getD] using List.getElem?_getD_replicate_default_eq (none : Option Bool) n i

theorem blankBlock_equivalent (n : ℕ) : (NativeBitGenerator.blankBlock n {}).Equivalent ({} : Tape) := by
  cases n with
  | zero => exact Tape.Equivalent.refl _
  | succ n =>
    change ({right := List.replicate n none ++ [none]} : Tape).Equivalent {}
    rw [← List.replicate_succ']
    exact Tape.blank_padding_equivalent [] (n + 1)

theorem entry_equivalent (v : OrderedGridVertex 32) (message : Bool) :
    (entry v message).Equivalent (Configuration.initial (rawInput v message)) :=
  ⟨rfl, rfl, (NativeControlledCipherInitial.preload_equivalent _ (blankBlock_equivalent 19)).trans
    (NativeControlledCipherInitial.preload_empty _), blankBlock_equivalent 19⟩

theorem handoff (v : OrderedGridVertex 32) (message : Bool) :
    ((prepared v message).resumeAt 0).Equivalent
      (NativeControlledEightBitCipher.entry v message {} {}) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact NativeControlledCipherInitial.preload_equivalent _
      ((erasedBefore_blank 39).trans NativeControlledCipherInitial.blank_workspace.symm)
  · exact (erasedBefore_blank 19).trans (Tape.blank_padding_equivalent [] 1).symm

theorem source_decision (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin source ((prepared v message).resumeAt 0) 442).map readDecision =
      (tableEightBitLaw v message).map (fun result => some (keyPairTest result)) := by
  unfold source readDecision
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (handoff v message) 442 _
    NativeKeyPairDecisionExecution.readDecision_equivalent]
  exact NativeKeyPairDecisionExecution.formatted_law v message {} {}

theorem framed_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code (entry v message) 930).map readDecision =
      (tableEightBitLaw v message).map (fun result => some (keyPairTest result)) := by
  unfold code entry
  rw [show 930 = 487 + 442 + 1 from rfl,
    NativeUniformSequence.run _ _ _ _ preparation_stops source_stops]
  change ((evalConfigWithin preparation (entry v message) 487).bind _).map readDecision = _
  rw [preparation_run, PMF.pure_bind, PMF.map_comp]
  simp only [Function.comp_def, readDecision_control]
  exact source_decision v message

theorem initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code (Configuration.initial (rawInput v message)) 930).map readDecision =
      (tableEightBitLaw v message).map (fun result => some (keyPairTest result)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (entry_equivalent v message).symm 930 _ readDecision_equivalent]
  exact framed_law v message

theorem haltsWithin (input : List Bool) : HaltsWithin code input 930 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 930
  polynomial := PolynomiallyBounded.const 930
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

theorem acceptance_law (v : OrderedGridVertex 32) (message : Bool) :
    eventProb ((evalConfigWithin code (Configuration.initial (rawInput v message)) 930).map readDecision)
      (· = some true) = eventProb ((tableEightBitLaw v message).map keyPairTest) (· = true) := by
  rw [initial_law, eventProb_map, eventProb_map]
  simp only [Option.some.injEq]

theorem first_acceptance (message : Bool) :
    (eventProb ((evalConfigWithin code (Configuration.initial (rawInput (sharpTableChain 0) message)) 930).map readDecision)
      (· = some true)).toReal = 1 := by
  rw [acceptance_law, keyPair_probability_first]

theorem second_acceptance (message : Bool) :
    (eventProb ((evalConfigWithin code (Configuration.initial (rawInput (sharpTableChain 2) message)) 930).map readDecision)
      (· = some true)).toReal = 91 / 128 := by
  rw [acceptance_law, keyPair_probability_second]

theorem gap_attained (message : Bool) :
    probabilityGap
      (eventProb ((evalConfigWithin code (Configuration.initial (rawInput (sharpTableChain 0) message)) 930).map readDecision) (· = some true))
      (eventProb ((evalConfigWithin code (Configuration.initial (rawInput (sharpTableChain 2) message)) 930).map readDecision) (· = some true)) =
        (37 / 128 : ℝ≥0∞) := by
  rw [acceptance_law, acceptance_law, keyPair_gap]

theorem edge_bound (u v : OrderedGridVertex 32)
    (he : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    probabilityGap
      (eventProb ((evalConfigWithin code (Configuration.initial (rawInput u message)) 930).map readDecision) (· = some true))
      (eventProb ((evalConfigWithin code (Configuration.initial (rawInput v message)) 930).map readDecision) (· = some true)) ≤
        (37 / 128 : ℝ≥0∞) := by
  rw [acceptance_law, acceptance_law]
  have h := table_all_observers_edge_bound u v he message (fun result => PMF.pure (keyPairTest result)) trivial
  simpa only [observerGap, PMF.map, Function.comp_def] using h

theorem outputBits_control (c : Configuration) (pc : ℕ) :
    ({c with pc := pc, halted := true} : Configuration).outputBits = c.outputBits := rfl

theorem source_packet (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin source ((prepared v message).resumeAt 0) 442).map Configuration.outputBits =
      (tableEightBitLaw v message).map (fun result => [!result.2, keyPairTest result]) := by
  unfold source
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (handoff v message) 442 _ (fun c d h => h.outputBits)]
  exact NativeKeyPairOutputPacket.framed_packet v message

theorem framed_packet (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code (entry v message) 930).map Configuration.outputBits =
      (tableEightBitLaw v message).map (fun result => [!result.2, keyPairTest result]) := by
  unfold code entry
  rw [show 930 = 487 + 442 + 1 from rfl,
    NativeUniformSequence.run _ _ _ _ preparation_stops source_stops]
  change ((evalConfigWithin preparation (entry v message) 487).bind _).map Configuration.outputBits = _
  rw [preparation_run, PMF.pure_bind, PMF.map_comp]
  simp only [Function.comp_def, outputBits_control]
  exact source_packet v message

theorem initial_packet (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code (Configuration.initial (rawInput v message)) 930).map Configuration.outputBits =
      (tableEightBitLaw v message).map (fun result => [!result.2, keyPairTest result]) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (entry_equivalent v message).symm 930 _ (fun c d h => h.outputBits)]
  exact framed_packet v message

theorem evalWithin_law (v : OrderedGridVertex 32) (message : Bool) :
    evalWithin code (rawInput v message) 930 =
      (tableEightBitLaw v message).map (fun result => some [!result.2, keyPairTest result]) := by
  rw [NativeKeyPairOutputPacket.evalWithin_of_halts _ _ _ (haltsWithin _)]
  change (evalConfigWithin code (Configuration.initial (rawInput v message)) 930).map
    (some ∘ Configuration.outputBits) = _
  rw [← PMF.map_comp, initial_packet, PMF.map_comp]
  rfl

theorem no_timeout (input : List Bool) :
    eventProb (evalWithin code input 930) (· = none) = 0 :=
  evalWithin_no_timeout code input 930 (haltsWithin input)

def acceptedPacket (raw : Option (List Bool)) : Prop := raw.bind (fun bits => bits[1]?) = some true

theorem evalWithin_acceptance (v : OrderedGridVertex 32) (message : Bool) :
    eventProb (evalWithin code (rawInput v message) 930) acceptedPacket =
      eventProb ((tableEightBitLaw v message).map keyPairTest) (· = true) := by
  rw [evalWithin_law, eventProb_map, eventProb_map]
  simp only [acceptedPacket, Option.bind_some, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq]

theorem evalWithin_gap_attained (message : Bool) :
    probabilityGap
      (eventProb (evalWithin code (rawInput (sharpTableChain 0) message) 930) acceptedPacket)
      (eventProb (evalWithin code (rawInput (sharpTableChain 2) message) 930) acceptedPacket) =
        (37 / 128 : ℝ≥0∞) := by
  rw [evalWithin_acceptance, evalWithin_acceptance, keyPair_gap]

end Machine.NativePreparedKeyDecision
