import Foundation.Crypto.Semantics.Machine.NativeSingleChallengeExecution
import Foundation.Crypto.Semantics.Machine.DelimitedResponseLoadingResources

/-! A faithful encoding and whole-prefix bound for the complete single-query
controller. Raw reply buffers, pending loader bits, actual blank tape cells,
control addresses and all three fixed code blocks are accounted for. -/
namespace Machine.NativeSingleChallenge.Resources
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

abbrev Fields := DelimitedResponseLoading.Resources.Fields

def pack : Control → Fields
  | .querying machine => (0, machine, [], false)
  | .seeking machine response => (1, machine, response, false)
  | .rewinding machine => (2, machine, [], false)
  | .executing machine => (3, machine, [], false)
  | .loading loader =>
      let fields := DelimitedResponseLoading.Resources.pack loader
      (fields.1 + 4, fields.2)

def unpack (fields : Fields) : Control :=
  match fields.1 with
  | 0 => .querying fields.2.1
  | 1 => .seeking fields.2.1 fields.2.2.1
  | 2 => .rewinding fields.2.1
  | 3 => .executing fields.2.1
  | tag => .loading (DelimitedResponseLoading.Resources.unpack (tag - 4, fields.2))

def encoding : FiniteBitEncoding Control :=
  DelimitedResponseLoading.Resources.fieldsEncoding.retract pack unpack (by
    intro state
    cases state with
    | loading loader => cases loader <;> rfl
    | _ => rfl)

def machine : Control → Configuration
  | .querying state | .seeking state _ | .rewinding state | .executing state => state
  | .loading loader => DelimitedResponseLoading.Resources.machine loader

def remaining : Control → List Bool
  | .seeking _ response => response
  | .loading loader => DelimitedResponseLoading.Resources.remaining loader
  | _ => []

/-- The reservation is only an analysis credit before the reply arrives.
It is not a buffer or advice stored in the actual querying state. -/
def extent (responseCap : Nat) : Control → Nat
  | .querying state => state.tapeCells + responseCap
  | state => (machine state).tapeCells + (remaining state).length

def pcIncrement (code : Program) : Nat :=
  code.addressCap + NativeBitstringSeekEnd.code.addressCap + rewindBitstring.addressCap + 1

variable (distribution : PMF (List Bool)) (code : Program) (responseCap : Nat)
    (hResponse : ∀ response ∈ distribution.support, response.length ≤ responseCap)

include hResponse in
theorem step_bounds (start next : Control) (h : next ∈ (step distribution code start).support) :
    (machine next).pc ≤ (machine start).pc + pcIncrement code ∧
      extent responseCap next ≤ extent responseCap start + 1 := by
  cases start with
  | querying state =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨response, hSupported, rfl⟩ := h
      have hLength := hResponse response hSupported
      simp only [machine, extent, remaining, pcIncrement]
      constructor <;> omega
  | seeking state response =>
      by_cases hHalt : state.halted = true
      · simp only [step, hHalt, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst next
        simp [machine, extent, remaining, DelimitedResponseLoading.Resources.machine,
          DelimitedResponseLoading.Resources.remaining, DelimitedResponseLoading.Resources.pack,
          Configuration.resumeAt, Configuration.tapeCells]
      · simp only [step, hHalt, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨after, hAfter, rfl⟩ := h
        have hp := pc_le_of_support NativeBitstringSeekEnd.code state after hAfter
        have hs := tapeCells_le_of_support NativeBitstringSeekEnd.code state after hAfter
        simp only [machine, extent, remaining, pcIncrement]
        constructor <;> omega
  | rewinding state =>
      by_cases hHalt : state.halted = true
      · simp only [step, hHalt, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst next
        simp [machine, extent, remaining, Configuration.resumeAt, Configuration.tapeCells]
      · simp only [step, hHalt, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨after, hAfter, rfl⟩ := h
        have hp := pc_le_of_support rewindBitstring state after hAfter
        have hs := tapeCells_le_of_support rewindBitstring state after hAfter
        simp only [machine, extent, remaining, List.length_nil, Nat.add_zero, pcIncrement]
        constructor <;> omega
  | executing state =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨after, hAfter, rfl⟩ := h
      have hp := pc_le_of_support code state after hAfter
      have hs := tapeCells_le_of_support code state after hAfter
      simp only [machine, extent, remaining, List.length_nil, Nat.add_zero, pcIncrement]
      constructor <;> omega
  | loading loader =>
      cases loader <;> simp only [step, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at h
      all_goals first
        | (obtain ⟨after, hAfter, rfl⟩ := h
           obtain ⟨hp, hs⟩ := DelimitedResponseLoading.Resources.step_bounds _ after hAfter
           simp only [machine, extent, remaining]
           unfold DelimitedResponseLoading.Resources.extent at hs
           unfold pcIncrement
           constructor <;> omega)
        | (subst next
           simp [machine, extent, remaining, DelimitedResponseLoading.Resources.machine,
             DelimitedResponseLoading.Resources.remaining, DelimitedResponseLoading.Resources.pack,
             Configuration.resumeAt, Configuration.tapeCells])

theorem encoding_length (state : Control) :
    (encoding.encode state).length ≤ 4 * (machine state).pc + 36 * extent responseCap state + 50 := by
  have hConfiguration := ConfigurationEncoding.configuration_length_le (machine state)
  have hMachine : (pack state).2.1 = machine state := by cases state <;> rfl
  have hRemaining : (pack state).2.2.1 = remaining state := by cases state <;> rfl
  have hTag : (pack state).1 ≤ 9 := by
    cases state with
    | loading loader => cases loader <;> simp [pack, DelimitedResponseLoading.Resources.pack]
    | _ => simp [pack]
  have hExtent : (machine state).tapeCells + (remaining state).length ≤ extent responseCap state := by
    cases state <;> simp [extent, remaining, machine]
  change (DelimitedResponseLoading.Resources.fieldsEncoding.encode
    ((pack state).1, (pack state).2.1, (pack state).2.2.1, (pack state).2.2.2)).length ≤ _
  simp only [DelimitedResponseLoading.Resources.fieldsEncoding, FiniteBitEncoding.prod_encode_length,
    ConfigurationEncoding.unary, List.length_replicate, FiniteBitEncoding.bitstring,
    ConfigurationEncoding.bit, id_eq, List.length_singleton, hMachine, hRemaining]
  omega

/-- Code includes the seek and rewind blocks as well as the consumer. -/
def completeEncoding : FiniteBitEncoding (Program × Control) :=
  (StructuredCodeEncoding.program.prod (StructuredCodeEncoding.program.prod StructuredCodeEncoding.program)).prod encoding
    |>.retract (fun pair => ((pair.1, NativeBitstringSeekEnd.code, rewindBitstring), pair.2))
      (fun pair => (pair.1.1, pair.2)) (fun _ => rfl)

def bitBound (initialPc initialCells horizon : Nat) : Nat :=
  4 * (StructuredCodeEncoding.program.encode code).length +
    4 * (StructuredCodeEncoding.program.encode NativeBitstringSeekEnd.code).length +
    2 * (StructuredCodeEncoding.program.encode rewindBitstring).length +
    4 * (initialPc + horizon * pcIncrement code) + 36 * (initialCells + responseCap + horizon) + 55

theorem bitBound_mono {cap nextCap pc nextPc cells nextCells time nextTime : Nat}
    (hCap : cap ≤ nextCap) (hPc : pc ≤ nextPc) (hCells : cells ≤ nextCells) (hTime : time ≤ nextTime) :
    bitBound code cap pc cells time ≤ bitBound code nextCap nextPc nextCells nextTime := by
  have hm := Nat.mul_le_mul_right (pcIncrement code) hTime
  unfold bitBound
  omega

theorem bitBound_polynomial {cap pc cells time : Nat → Nat}
    (hCap : PolynomiallyBounded cap) (hPc : PolynomiallyBounded pc)
    (hCells : PolynomiallyBounded cells) (hTime : PolynomiallyBounded time) :
    PolynomiallyBounded (fun n => bitBound code (cap n) (pc n) (cells n) (time n)) :=
  (((((PolynomiallyBounded.const (4 * (StructuredCodeEncoding.program.encode code).length)).add
    (PolynomiallyBounded.const (4 * (StructuredCodeEncoding.program.encode NativeBitstringSeekEnd.code).length))).add
    (PolynomiallyBounded.const (2 * (StructuredCodeEncoding.program.encode rewindBitstring).length))).add
    ((PolynomiallyBounded.const 4).mul (hPc.add (hTime.mul (PolynomiallyBounded.const (pcIncrement code)))))).add
    ((PolynomiallyBounded.const 36).mul ((hCells.add hCap).add hTime))).add (PolynomiallyBounded.const 55)

include hResponse in
theorem peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (prefixBits : List Bool) (state : Control)
    (h : state ∈ (eval (step distribution code) elapsed (initial prefixBits)).support) :
    (completeEncoding.encode (code, state)).length ≤
      bitBound code responseCap 0 (Configuration.initial prefixBits).tapeCells horizon := by
  have hp := ResourceGrowth.prefix_bound (step distribution code) (fun state => (machine state).pc)
    (pcIncrement code) (fun before after hs => (step_bounds distribution code responseCap hResponse before after hs).1)
    horizon elapsed hElapsed (initial prefixBits) state h
  have hs := ResourceGrowth.prefix_bound (step distribution code) (extent responseCap) 1
    (fun before after hs => (step_bounds distribution code responseCap hResponse before after hs).2)
    horizon elapsed hElapsed (initial prefixBits) state h
  have he := encoding_length responseCap state
  change (machine state).pc ≤ 0 + horizon * pcIncrement code at hp
  change extent responseCap state ≤ (Configuration.initial prefixBits).tapeCells + responseCap + horizon * 1 at hs
  simp only [Nat.zero_add, Nat.mul_one] at hp hs
  change ( (StructuredCodeEncoding.program.prod (StructuredCodeEncoding.program.prod StructuredCodeEncoding.program)).prod encoding
    |>.encode ((code, NativeBitstringSeekEnd.code, rewindBitstring), state)).length ≤ _
  simp only [FiniteBitEncoding.prod_encode_length]
  unfold bitBound
  omega

end Machine.NativeSingleChallenge.Resources
