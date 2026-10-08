import Foundation.Examples.OneUseInvocation
import Foundation.Constructions.Symmetric.OneTimePad
import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.KeyedContinuation

/-! Actual arbitrary-width normal encryption after an independently proved
public prefix. Messages may depend on the public prefix state. Physical
handoff is required for every supported selected state and sampled key. -/
namespace Foundation.OneUseAdaptiveSecrecyExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Public : Type v} {Input : Type w} {width : Nat}
    (code : Code) (oracle : BitOracle State) (state : Public → State)
    (trace : Public → List (List Bool × List Bool)) (message : Public → Bits width)
    (machine : Public → Bits width → Machine.Configuration)
    (active : ∀ value bits, (machine value bits).halted = false)
    (instruction : ∀ value bits, code[(machine value bits).pc]? = some .call)
    (tape : ∀ value bits, (machine value bits).outputTape = RequestExport.packetTape [] [] bits.toList)
    (nextHalt : ∀ value bits, code[(machine value bits).advance.pc]? = some (.native .halt))

def operands (message key : Bits width) : Machine.PairPreparation.Input :=
  ⟨key.toList, message.toList, [], [], by simp⟩

noncomputable def normal (key : Bits width) :
    Procedure (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) Public Unit :=
  Procedure.ofFixed _
    (fun value => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨state value, .running (machine value (message value)), trace value⟩)
    (fun value _ => OneUseInvocationExamples.final (machine value (message value))
      (state value) (trace value) (operands (message value) key))
    (fun _ => PMF.pure ()) (fun _ => 33 * width + 34)
    (fun value => by
      simpa only [operands, Bits.length_toList, PMF.pure_map] using
        OneUseInvocationExamples.run code oracle (machine value (message value))
          (state value) (trace value) (operands (message value) key)
          (active value (message value)) (instruction value (message value))
          (tape value (message value)) (nextHalt value (message value)))

def packet : OneUseSource.Control State → List Bool
  | .source _ _ frame => match frame.control with
    | .running current => current.outputBits
    | _ => []
  | _ => []

noncomputable def response (key : Bits width) (publicState : Public) (output : Unit) : List Bool :=
  packet ((normal code oracle state trace message machine active instruction tape nextHalt key).exit publicState output)

noncomputable def publicNormal : PMF (List Bool × Nat) :=
  (uniform (Bits width)).map (fun bits => (true :: bits.toList, 33 * width + 34))

theorem normal_public_cost (publicState : Public) :
    (uniform (Bits width)).bind (fun key =>
      ((normal code oracle state trace message machine active instruction tape nextHalt key).costed publicState).map
        (fun result => (response code oracle state trace message machine active instruction tape nextHalt
          key publicState result.1, result.2))) = publicNormal (width := width) := by
  have he : ∀ key : Bits width,
      response code oracle state trace message machine active instruction tape nextHalt key publicState () =
        true :: (Foundation.Symmetric.OneTimePad.encrypt key (message publicState)).toList := by
    intro key
    simp only [response, normal, Procedure.ofFixed, packet, OneUseInvocationExamples.final,
      operands, Machine.Configuration.outputBits, ResponseLoading.loaded, ResponseLoading.fromCells,
      Machine.Tape.bits, Foundation.Symmetric.OneTimePad.encrypt]
    simp [Machine.OneTimePad.toList_xor]
  change (uniform (Bits width)).bind (fun key =>
    ((PMF.pure ()).map (fun _ => ((), 33 * width + 34))).map (fun result =>
      (response code oracle state trace message machine active instruction tape nextHalt key publicState result.1, result.2))) = _
  simp only [PMF.pure_map]
  simp_rw [he]
  change (uniform (Bits width)).map (fun key =>
    (true :: (Foundation.Symmetric.OneTimePad.encrypt key (message publicState)).toList, 33 * width + 34)) = _
  have h := congrArg (fun distribution => distribution.map
    (fun bits : Bits width => (true :: bits.toList, 33 * width + 34)))
    (Foundation.Symmetric.OneTimePad.ciphertext_uniform (message publicState))
  simpa only [Foundation.Symmetric.OneTimePad.ciphertext, publicNormal, PMF.map_comp, Function.comp_def] using h

variable
    (before : Bits width → Procedure
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) Input Public)
    (handoff : ∀ key start publicState, publicState ∈ ((before key).semantics start).support →
      (normal code oracle state trace message machine active instruction tape nextHalt key).entry publicState = (before key).exit start publicState)

noncomputable def complete (key : Bits width) :=
  (before key).seq (normal code oracle state trace message machine active instruction tape nextHalt key) (handoff key)
    (fun _ => 33 * width + 34) (fun _ _ _ => Nat.le_refl _)

noncomputable def publicRun (start : Input) :=
  (uniform (Bits width)).bind (fun key => ((complete code oracle state trace message machine active instruction tape nextHalt before handoff key).costed start).map
    (fun result => ((result.1.1, response code oracle state trace message machine active instruction tape nextHalt key result.1.1 result.1.2), result.2)))

theorem public_run (start : Input) (commonPrefix : PMF (Public × Nat))
    (hPrefix : ∀ key, (before key).costed start = commonPrefix) :
    publicRun code oracle state trace message machine active instruction tape nextHalt before handoff start =
      commonPrefix.bind (fun first => (publicNormal (width := width)).map
        (fun second => ((first.1, second.1), first.2 + second.2))) := by
  apply Procedure.keyed_seq_public_cost (uniform (Bits width)) before
    (normal code oracle state trace message machine active instruction tape nextHalt) handoff (fun _ _ => 33 * width + 34)
    (fun _ _ _ _ => Nat.le_refl _) (response code oracle state trace message machine active instruction tape nextHalt) start
    commonPrefix (fun _ => publicNormal (width := width)) hPrefix
  exact normal_public_cost code oracle state trace message machine active instruction tape nextHalt

/-- At any common horizon above the two charged bounds, the original
machine's response agrees with the response of the composed contract. -/
theorem machine_run (start : Input) (horizon : Nat)
    (hBudget : ∀ key, (before key).budget start + (33 * width + 34) ≤ horizon) :
    (uniform (Bits width)).bind (fun key =>
      (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
        horizon ((before key).entry start)).map packet) =
      (publicRun code oracle state trace message machine active instruction tape nextHalt before handoff start).map
        (fun result => result.1.2) := by
  unfold publicRun
  rw [PMF.map_bind]
  congr 1
  funext key
  have h := (complete code oracle state trace message machine active instruction tape nextHalt before handoff key).final_run
    start (fun _ _ => by
      simp [complete, Procedure.seq, normal, Procedure.ofFixed, OneUseInvocationExamples.final,
        OneUseSource.step, Reification.timedStep, Reification.terminal, PMF.pure_map])
    horizon (hBudget key)
  change (TimedExecution.eval _ _ ((complete code oracle state trace message machine active instruction tape nextHalt before handoff key).entry start)).map _ = _
  rw [h, ← Procedure.correct, PMF.map_comp, PMF.map_comp, PMF.map_comp]
  rfl

theorem perfect_secrecy (left right : Public → Bits width)
    (leftBefore rightBefore : Bits width → Procedure
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) Input Public)
    (leftHandoff : ∀ key start publicState, publicState ∈ ((leftBefore key).semantics start).support →
      (normal code oracle state trace left machine active instruction tape nextHalt key).entry publicState = (leftBefore key).exit start publicState)
    (rightHandoff : ∀ key start publicState, publicState ∈ ((rightBefore key).semantics start).support →
      (normal code oracle state trace right machine active instruction tape nextHalt key).entry publicState = (rightBefore key).exit start publicState)
    (start : Input) (commonPrefix : PMF (Public × Nat))
    (hLeft : ∀ key, (leftBefore key).costed start = commonPrefix)
    (hRight : ∀ key, (rightBefore key).costed start = commonPrefix) :
    publicRun code oracle state trace left machine active instruction tape nextHalt leftBefore leftHandoff start =
      publicRun code oracle state trace right machine active instruction tape nextHalt rightBefore rightHandoff start := by
  rw [public_run code oracle state trace left machine active instruction tape nextHalt leftBefore leftHandoff start commonPrefix hLeft,
    public_run code oracle state trace right machine active instruction tape nextHalt rightBefore rightHandoff start commonPrefix hRight]

theorem machine_perfect_secrecy (left right : Public → Bits width)
    (leftBefore rightBefore : Bits width → Procedure
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) Input Public)
    (leftHandoff : ∀ key start publicState, publicState ∈ ((leftBefore key).semantics start).support →
      (normal code oracle state trace left machine active instruction tape nextHalt key).entry publicState = (leftBefore key).exit start publicState)
    (rightHandoff : ∀ key start publicState, publicState ∈ ((rightBefore key).semantics start).support →
      (normal code oracle state trace right machine active instruction tape nextHalt key).entry publicState = (rightBefore key).exit start publicState)
    (start : Input) (commonPrefix : PMF (Public × Nat))
    (hLeft : ∀ key, (leftBefore key).costed start = commonPrefix)
    (hRight : ∀ key, (rightBefore key).costed start = commonPrefix)
    (horizon : Nat)
    (leftBudget : ∀ key, (leftBefore key).budget start + (33 * width + 34) ≤ horizon)
    (rightBudget : ∀ key, (rightBefore key).budget start + (33 * width + 34) ≤ horizon)
    (observer : List Bool → PMF Bool) :
    ((uniform (Bits width)).bind (fun key =>
      (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
        horizon ((leftBefore key).entry start)).map packet)).bind observer =
    ((uniform (Bits width)).bind (fun key =>
      (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
        horizon ((rightBefore key).entry start)).map packet)).bind observer := by
  rw [machine_run code oracle state trace left machine active instruction tape nextHalt leftBefore leftHandoff start horizon leftBudget,
    machine_run code oracle state trace right machine active instruction tape nextHalt rightBefore rightHandoff start horizon rightBudget]
  rw [perfect_secrecy code oracle state trace machine active instruction tape nextHalt left right
    leftBefore rightBefore leftHandoff rightHandoff start commonPrefix hLeft hRight]

end Foundation.OneUseAdaptiveSecrecyExamples
