import Foundation.Constructions.Symmetric.EncryptThenMAC.OneUsePad
import Foundation.Crypto.Semantics.Oracle.OneUseXorInvocation
import Foundation.Crypto.Semantics.Oracle.ControllerResourceSimulation
import Foundation.Crypto.Semantics.ProcedurePhysical

/-! Arbitrary-width one-use pad encryption at a real source call instruction.
Fresh and spent requests have one common physical-output contract. The
private key is already in its store; native generation is a separate charged
contract. Every supported call, delivery and continuation is the actual VM. -/
namespace Foundation.Symmetric.EncryptThenMAC.OneUsePadInvocation
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def operands {length : Nat} (key message : Bits length) : Machine.PairPreparation.Input where
  first := key.toList
  second := message.toList
  firstTail := []
  secondTail := []
  sameLength := by simp

def keyStore {length : Nat} (key : Bits length) : Tape :=
  Machine.PairPreparation.operand [] key.toList []

def requestTape {length : Nat} (message : Bits length) : Tape :=
  RequestExport.packetTape [] [] message.toList

def packet {length : Nat} (spent : Bool) (key message : Bits length) : List Bool :=
  if spent then [false] else true :: (Foundation.Symmetric.OneTimePad.encrypt key message).toList

theorem packet_encrypt (width : Nat → Nat) (n : Nat) (spent : Bool)
    (key message : Bits (width n)) :
    packet spent key message =
      match ((OneUsePad.scheme width).encrypt n key spent message).2 with
      | none => [false]
      | some ciphertext => true :: ciphertext.toList := by
  cases spent <;> rfl

variable (code : Code) (oracle : BitOracle State) (machine : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool))
    {length : Nat} (key message : Bits length)
    (hActive : machine.halted = false) (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = requestTape message)

def result (spent : Bool) : OneUseSource.Control State :=
  .source true (keyStore key)
    (NativeCallback.resumed machine.advance state trace message.toList (packet spent key message))

noncomputable def invocation (spent : Bool) :
    Procedure (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      Unit (OneUseSource.Control State) :=
  if spent then
    (OneUseSource.spentInvocation Machine.OneTimePad.Prepared.listProcedure.code code oracle
      (keyStore key) machine state trace message.toList [] [] hActive hCall hTape).physical
  else
    (OneUseXorInvocation.invocation code oracle machine state trace
      (operands key message) hActive hCall hTape).physical

theorem entry (spent : Bool) :
    (invocation code oracle machine state trace key message hActive hCall hTape spent).entry () =
      .source spent (keyStore key) ⟨state, .running machine, trace⟩ := by
  cases spent <;> rfl

theorem budget (spent : Bool) :
    (invocation code oracle machine state trace key message hActive hCall hTape spent).budget () =
      if spent then 2 * length + 22 else 33 * length + 33 := by
  cases spent <;> simp only [invocation, Bool.false_eq_true, ↓reduceIte, Procedure.physical_budget]
  · rw [OneUseXorInvocation.budget]
    simp [operands]
  · rw [OneUseSource.spentInvocation_budget]
    simp

/-- The returned response realizes the typed one-use scheme at every width,
including zero. Actual saved caller data and the private store are retained. -/
theorem semantics (spent : Bool) :
    (invocation code oracle machine state trace key message hActive hCall hTape spent).semantics () =
      PMF.pure (result machine state trace key message spent) := by
  cases spent <;> simp only [invocation, Bool.false_eq_true, ↓reduceIte, Procedure.physical_semantics]
  · rw [OneUseXorInvocation.distribution]
    simp only [result, keyStore, packet, Bool.false_eq_true, ↓reduceIte, operands,
      Foundation.Symmetric.OneTimePad.encrypt, Machine.OneTimePad.toList_xor]
  · rw [OneUseSource.spentInvocation_distribution]
    rfl

/-- Continuation runs on the same machine after the actual charged return;
no synthetic stop or restarted source VM is introduced. -/
theorem resume (spent : Bool) (horizon : Nat)
    (hBudget : (if spent then 2 * length + 22 else 33 * length + 33) ≤ horizon) :
    TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      horizon (.source spent (keyStore key) ⟨state, .running machine, trace⟩) =
      ((invocation code oracle machine state trace key message hActive hCall hTape spent).costed ()).bind
        (fun returned => TimedExecution.eval
          (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
          (horizon - returned.2) returned.1) := by
  have h := (invocation code oracle machine state trace key message hActive hCall hTape spent).law
    () horizon (by rw [budget]; exact hBudget)
  rw [entry] at h
  cases spent <;> exact h

/-- The common retained-data theorem covers every real intermediate call
state, including physical preparation, native XOR and response delivery. -/
theorem memory_peak (spent : Bool) (stateSize : State → Nat) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request answer, answer ∈ (oracle state request).support →
      stateSize answer.1 ≤ stateSize state + stateIncrement ∧ answer.2.length ≤ responseCap)
    (elapsed : Nat) (hElapsed : elapsed ≤ (if spent then 2 * length + 22 else 33 * length + 33))
    (target : OneUseSource.Control State)
    (h : target ∈ (TimedExecution.eval
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) elapsed
      (.source spent (keyStore key) ⟨state, .running machine, trace⟩)).support) :
    ControllerStorage.sourceCells stateSize target ≤
      4 * (ControllerExtent.sourceExtent stateSize
        (.source spent (keyStore key) ⟨state, .running machine, trace⟩) +
          (if spent then 2 * length + 22 else 33 * length + 33) * (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (ControllerExtent.sourceExtent stateSize
        (.source spent (keyStore key) ⟨state, .running machine, trace⟩) +
          (if spent then 2 * length + 22 else 33 * length + 33) * (stateIncrement + responseCap + 2)) + 2 :=
  (ControllerExtent.sourceEnvelope stateSize Machine.OneTimePad.Prepared.listProcedure.code code oracle
    stateIncrement responseCap hOracle).peak _ elapsed hElapsed _ target h

end Foundation.Symmetric.EncryptThenMAC.OneUsePadInvocation
