import Foundation.Crypto.Semantics.Oracle.EncodedStorage
import Foundation.Crypto.Semantics.Machine.StructuredCodeEncoding

/-! Efficient faithful code-and-state representation of arbitrary oracle
callers. Encode instructions individually rather than using the legacy unary
index of the entire program. Actual intermediate buffers, tapes, transcript
and the client-specified oracle-state representation are all included. -/
namespace CryptoOracle.Interactive.StructuredCodeStorage
open Machine Foundation.Probability
universe u
set_option backward.isDefEq.respectTransparency false

private def pack : Instruction → Bool × Machine.Instruction
  | .native i => (false, i)
  | .call => (true, .halt)

private def unpack (fields : Bool × Machine.Instruction) : Instruction :=
  if fields.1 then .call else .native fields.2

def instruction : FiniteBitEncoding Instruction :=
  (Machine.ConfigurationEncoding.bit.prod Machine.StructuredCodeEncoding.instruction).retract pack unpack
    (by intro i; cases i <;> rfl)

def codeEncoding : FiniteBitEncoding Code := instruction.list

theorem instruction_length (i : Instruction) :
    (instruction.encode i).length ≤ 5 * (match i with | .native i => i.addressCap | .call => 0) + 26 := by
  cases i with
  | native i =>
      have h := Machine.StructuredCodeEncoding.instruction_length_le i
      change ((Machine.ConfigurationEncoding.bit.prod Machine.StructuredCodeEncoding.instruction).encode (false, i)).length ≤ _
      simp only [FiniteBitEncoding.prod_encode_length, Machine.ConfigurationEncoding.bit, List.length_singleton]
      omega
  | call => decide

theorem code_length (code : Code) :
    (codeEncoding.encode code).length ≤ 10 * EncodedStorage.addressCap code + 54 * code.length + 1 := by
  induction code with
  | nil => decide
  | cons i rest ih =>
      have hi := instruction_length i
      change (instruction.list.encode (i :: rest)).length ≤ _
      rw [FiniteBitEncoding.list_encode_cons_length]
      change 2 * (instruction.encode i).length + 2 + (codeEncoding.encode rest).length ≤ _
      cases i <;> simp only [EncodedStorage.addressCap, List.length_cons] <;> dsimp at hi <;> omega

def completeEncoding {State : Type u} (E : FiniteBitEncoding State) : FiniteBitEncoding (Code × Configuration State) :=
  codeEncoding.prod (ConfigurationEncoding.frame E)

def bound (code : Code) (initialPc initialExtent horizon stateIncrement responseCap : Nat) : Nat :=
  let cap := initialExtent + horizon * (stateIncrement + responseCap + 2)
  2 * (codeEncoding.encode code).length + 8 * (initialPc + horizon * (EncodedStorage.addressCap code + 1)) +
    72 * (2 * cap ^ 2 + 5 * cap + 1) + 4 * cap + 101

theorem bound_mono (code : Code) {pc nextPc extent nextExtent time nextTime increment nextIncrement response nextResponse : Nat}
    (hPc : pc ≤ nextPc) (hExtent : extent ≤ nextExtent) (hTime : time ≤ nextTime)
    (hIncrement : increment ≤ nextIncrement) (hResponse : response ≤ nextResponse) :
    bound code pc extent time increment response ≤ bound code nextPc nextExtent nextTime nextIncrement nextResponse := by
  have hFactor : increment + response + 2 ≤ nextIncrement + nextResponse + 2 := by omega
  have hCap := Nat.add_le_add hExtent (Nat.mul_le_mul hTime hFactor)
  have hAddress := Nat.mul_le_mul_right (EncodedStorage.addressCap code + 1) hTime
  have hSquare := Nat.pow_le_pow_left hCap 2
  dsimp only [bound]
  omega

theorem peak {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : Code) (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start target : Configuration State)
    (hTarget : target ∈ (TimedExecution.eval (Reification.timedStep code oracle) elapsed start).support) :
    ((completeEncoding E).encode (code, target)).length ≤
      bound code (ConfigurationEncoding.pc start.control) (ControllerExtent.frameExtent stateSize start)
        horizon stateIncrement responseCap := by
  have hp := TimedExecution.ResourceGrowth.prefix_bound (Reification.timedStep code oracle)
    (fun c => ConfigurationEncoding.pc c.control) (EncodedStorage.addressCap code + 1) (EncodedStorage.pc_step code oracle)
    horizon elapsed hElapsed start target hTarget
  have he := TimedExecution.ResourceGrowth.prefix_bound (Reification.timedStep code oracle)
    (ControllerExtent.frameExtent stateSize) (stateIncrement + responseCap + 2)
    (fun a b h => by simpa only [Nat.add_assoc] using
      ControllerExtent.public_step stateSize code oracle stateIncrement responseCap hOracle a b h)
    horizon elapsed hElapsed start target hTarget
  have hf := ConfigurationEncoding.frame_extent_length_le E stateSize hState target
  have hq := Nat.pow_le_pow_left he 2
  change (codeEncoding.prod (ConfigurationEncoding.frame E) |>.encode (code, target)).length ≤ _
  rw [FiniteBitEncoding.prod_encode_length]
  dsimp only [bound]
  omega

theorem bound_polynomial (code : Code)
    {initialPc initialExtent horizon stateIncrement responseCap : Nat → Nat}
    (hPc : PolynomiallyBounded initialPc) (hExtent : PolynomiallyBounded initialExtent)
    (hTime : PolynomiallyBounded horizon) (hIncrement : PolynomiallyBounded stateIncrement)
    (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => bound code (initialPc n) (initialExtent n) (horizon n)
      (stateIncrement n) (responseCap n)) := by
  have hc := hExtent.add (hTime.mul ((hIncrement.add hResponse).add (PolynomiallyBounded.const 2)))
  have hp := hPc.add (hTime.mul (PolynomiallyBounded.const (EncodedStorage.addressCap code + 1)))
  have hq := (((PolynomiallyBounded.const 2).mul (hc.mul hc)).add
    ((PolynomiallyBounded.const 5).mul hc)).add (PolynomiallyBounded.const 1)
  have hb := (((((PolynomiallyBounded.const (2 * (codeEncoding.encode code).length)).add
    ((PolynomiallyBounded.const 8).mul hp)).add ((PolynomiallyBounded.const 72).mul hq)).add
      ((PolynomiallyBounded.const 4).mul hc)).add (PolynomiallyBounded.const 101))
  simpa only [bound, pow_two] using hb

end CryptoOracle.Interactive.StructuredCodeStorage
