import Foundation.Crypto.Semantics.Oracle.ConfigurationEncoding
import Foundation.Crypto.Semantics.Oracle.ControllerExtentExecution
import Foundation.Crypto.Semantics.Machine.ControlStorage

/-! Complete bit-representation bounds for actual public oracle execution.
External state size must cover its codec; oracle state growth and response
length are explicit assumptions. Private-key callback controllers are separate. -/
namespace CryptoOracle.Interactive.EncodedStorage
open Foundation.Probability Machine
universe u
set_option backward.isDefEq.respectTransparency false

def addressCap : Code → Nat
  | [] => 0
  | .call :: rest => addressCap rest
  | .native i :: rest => i.addressCap + addressCap rest

theorem address_le (code : Code) (i : Machine.Instruction) (h : Instruction.native i ∈ code) :
    i.addressCap ≤ addressCap code := by
  induction code with
  | nil => simp at h
  | cons head rest ih =>
      cases head with
      | call =>
          simp only [List.mem_cons] at h
          rcases h with h | h
          · cases h
          · exact ih h
      | native instruction =>
          simp only [List.mem_cons, Instruction.native.injEq] at h
          rcases h with rfl | h
          · simp [addressCap]
          · have ht := ih h
            simp only [addressCap]
            omega

theorem pc_step {State : Type u} (code : Code) (oracle : BitOracle State)
    (start next : Configuration State) (h : next ∈ (Reification.timedStep code oracle start).support) :
    ConfigurationEncoding.pc next.control ≤ ConfigurationEncoding.pc start.control + (addressCap code + 1) := by
  rcases start with ⟨state, control, trace⟩
  cases control with
  | running machine =>
      cases hh : machine.halted with
      | true =>
          simp [Reification.timedStep, Reification.terminal, hh] at h
          subst next
          omega
      | false =>
          cases hi : code[machine.pc]? with
          | none =>
              simp [Reification.timedStep, Reification.terminal, Reification.perform,
                Reification.action, transition, hh, hi] at h
              subst next
              simp [ConfigurationEncoding.pc]
          | some instruction =>
              cases instruction with
              | call =>
                  simp [Reification.timedStep, Reification.terminal, Reification.perform,
                    Reification.action, transition, hh, hi] at h
                  subst next
                  simp [ConfigurationEncoding.pc, Machine.Configuration.advance]
              | native instruction =>
                  have hb := address_le code instruction (List.mem_of_getElem? hi)
                  cases hn : instruction.next machine with
                  | inl target =>
                      have hp := Machine.pc_le_of_instruction instruction machine target (by simp [hn])
                      simp [Reification.timedStep, Reification.terminal, Reification.perform,
                        Reification.action, transition, hh, hi, hn] at h
                      subst next
                      simp only [ConfigurationEncoding.pc]
                      omega
                  | inr pair =>
                      rcases pair with ⟨zero, one⟩
                      have hz := Machine.pc_le_of_instruction instruction machine zero (by simp [hn])
                      have ho := Machine.pc_le_of_instruction instruction machine one (by simp [hn])
                      simp only [Reification.timedStep, Reification.terminal, hh, Bool.false_eq_true,
                        ↓reduceIte, Reification.perform, Reification.action, transition, hi, hn,
                        PMF.mem_support_map_iff] at h
                      obtain ⟨bit, _, he⟩ := h
                      subst next
                      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, ConfigurationEncoding.pc] <;> omega
  | sending machine tape reversed =>
      cases ht : tape.current <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition, ht] at h <;> subst next <;> simp [ConfigurationEncoding.pc]
  | reversing machine remaining request =>
      cases remaining <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition] at h <;> subst next <;> simp [ConfigurationEncoding.pc]
  | awaiting machine request =>
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, PMF.mem_support_map_iff] at h
      obtain ⟨result, _, he⟩ := h
      subst next
      simp [ConfigurationEncoding.pc]
  | loading machine remaining tape =>
      cases remaining <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition] at h <;> subst next <;> simp [ConfigurationEncoding.pc]
  | advancing machine remaining tape =>
      simp [Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition] at h
      subst next
      simp [ConfigurationEncoding.pc]
  | rewinding machine tape =>
      cases ht : tape.left <;>
        simp [Reification.timedStep, Reification.terminal, Reification.perform,
          Reification.action, transition, ht] at h <;> subst next <;> simp [ConfigurationEncoding.pc]
  | finished result =>
      simp [Reification.timedStep, Reification.terminal] at h
      subst next
      omega

def codeEncoding : FiniteBitEncoding Code where
  encode := fun code => List.replicate (Encodable.encode code) true
  decode := fun raw => if raw = List.replicate raw.length true then Encodable.decode raw.length else none
  decode_encode := by intro code; simp

def bound (code : Code) (initialPc initialExtent horizon stateIncrement responseCap : Nat) : Nat :=
  let cap := initialExtent + horizon * (stateIncrement + responseCap + 2)
  (codeEncoding.encode code).length + 8 * (initialPc + horizon * (addressCap code + 1)) +
    72 * (2 * cap ^ 2 + 5 * cap + 1) + 4 * cap + 100

theorem encoded_peak {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : Code) (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start target : Configuration State)
    (hTarget : target ∈ (TimedExecution.eval (Reification.timedStep code oracle) elapsed start).support) :
    (codeEncoding.encode code).length + ((ConfigurationEncoding.frame E).encode target).length ≤
      bound code (ConfigurationEncoding.pc start.control) (ControllerExtent.frameExtent stateSize start)
        horizon stateIncrement responseCap := by
  have hp := TimedExecution.ResourceGrowth.prefix_bound (Reification.timedStep code oracle)
    (fun c => ConfigurationEncoding.pc c.control) (addressCap code + 1) (pc_step code oracle)
    horizon elapsed hElapsed start target hTarget
  have he := TimedExecution.ResourceGrowth.prefix_bound (Reification.timedStep code oracle)
    (ControllerExtent.frameExtent stateSize) (stateIncrement + responseCap + 2)
    (fun a b h => by simpa only [Nat.add_assoc] using
      ControllerExtent.public_step stateSize code oracle stateIncrement responseCap hOracle a b h)
    horizon elapsed hElapsed start target hTarget
  have hf := ConfigurationEncoding.frame_extent_length_le E stateSize hState target
  have hq := Nat.pow_le_pow_left he 2
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
  have hp := hPc.add (hTime.mul (PolynomiallyBounded.const (addressCap code + 1)))
  have hq := (((PolynomiallyBounded.const 2).mul (hc.mul hc)).add
    ((PolynomiallyBounded.const 5).mul hc)).add (PolynomiallyBounded.const 1)
  have hb := (((((PolynomiallyBounded.const (codeEncoding.encode code).length).add
    ((PolynomiallyBounded.const 8).mul hp)).add ((PolynomiallyBounded.const 72).mul hq)).add
      ((PolynomiallyBounded.const 4).mul hc)).add (PolynomiallyBounded.const 100))
  simpa only [bound, pow_two] using hb

end CryptoOracle.Interactive.EncodedStorage
