import Foundation.Crypto.Semantics.Machine.Masking
import Foundation.Crypto.Semantics.Machine.ControlStorage

/-! Faithful bit representation and all-prefix resource bounds for the
finite masking controller, including preparation before native execution.
All stored lists, intermediate tape cells and program counters are retained.
Encoding is a mathematical observation, not an executable host operation. -/
namespace Machine.Masking
open Foundation.Probability

def bitList : FiniteBitEncoding (List Bool) := ⟨id, some, fun _ => rfl⟩
def fields :=
  (bitList.prod (bitList.prod (bitList.prod bitList))).sum
    ((bitList.prod (bitList.prod bitList)).sum
      ((bitList.prod ConfigurationEncoding.tape).sum ConfigurationEncoding.configuration))

def configurationEncoding : FiniteBitEncoding Configuration where
  encode := fun config => fields.encode (match config with
    | .prefix header mask challenge acc => .inl (header, mask, challenge, acc)
    | .masking mask challenge acc => .inr (.inl (mask, challenge, acc))
    | .loading acc tape => .inr (.inr (.inl (acc, tape)))
    | .running machine => .inr (.inr (.inr machine)))
  decode := fun raw => (fields.decode raw).map fun value => match value with
    | .inl (header, mask, challenge, acc) => .prefix header mask challenge acc
    | .inr (.inl (mask, challenge, acc)) => .masking mask challenge acc
    | .inr (.inr (.inl (acc, tape))) => .loading acc tape
    | .inr (.inr (.inr machine)) => .running machine
  decode_encode := by intro config; cases config <;> simp [fields.decode_encode]

def codeEncoding : FiniteBitEncoding Code where
  encode := fun code => match code with
    | .native program => false :: Program.encode program
    | .masked side program => true :: side :: Program.encode program
  decode := fun raw => match raw with
    | false :: rest => (Program.decode rest).map Code.native
    | true :: side :: rest => (Program.decode rest).map (Code.masked side)
    | _ => none
  decode_encode := by intro code; cases code <;> simp

def Configuration.retained : Configuration → Nat
  | .prefix header mask challenge acc => header.length + mask.length + challenge.length + acc.length + 2
  | .masking mask challenge acc => mask.length + challenge.length + acc.length + 2
  | .loading acc tape => acc.length + tape.cells + 1
  | .running machine => machine.tapeCells

def Configuration.pc : Configuration → Nat
  | .running machine => machine.pc
  | _ => 0

theorem prepend_cells_le (bit : Bool) (tape : Tape) :
    (prepend bit tape).cells ≤ tape.cells + 1 := by
  cases tape with
  | mk left current right =>
      cases current <;> cases right <;> simp [prepend, Tape.cells] <;> omega

theorem retained_nextController (config : Configuration) :
    (nextController config).retained ≤ config.retained + 1 := by
  cases config with
  | «prefix» header mask challenge acc =>
      cases header with
      | nil => simp [nextController, Configuration.retained]
      | cons bit rest => simp [nextController, Configuration.retained]; omega
  | masking mask challenge acc =>
      cases mask <;> cases challenge <;> simp [nextController, Configuration.retained, Tape.cells] <;> omega
  | loading acc tape =>
      cases acc with
      | nil => simp [nextController, Configuration.retained, Machine.Configuration.tapeCells, Tape.cells]
      | cons bit rest =>
          have hp := prepend_cells_le bit tape
          simp only [nextController, Configuration.retained, List.length_cons]
          omega
  | running machine => simp [nextController]

theorem retained_step (code : Code) (start target : Configuration)
    (h : target ∈ (step code start).support) : target.retained ≤ start.retained + 1 := by
  cases start with
  | running machine =>
      rw [step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hNext, rfl⟩ := h
      exact Machine.tapeCells_le_of_support code.program machine next hNext
  | «prefix» header mask challenge acc =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst target
      exact retained_nextController _
  | masking mask challenge acc =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst target
      exact retained_nextController _
  | loading acc tape =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst target
      exact retained_nextController _

theorem pc_step (code : Code) (start target : Configuration)
    (h : target ∈ (step code start).support) :
    target.pc ≤ start.pc + (code.program.addressCap + 1) := by
  cases start with
  | running machine =>
      rw [step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hNext, rfl⟩ := h
      exact Machine.pc_le_of_support code.program machine next hNext
  | «prefix» header mask challenge acc =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst target
      cases header <;> simp [nextController, Configuration.pc]
  | masking mask challenge acc =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst target
      cases mask <;> cases challenge <;> simp [nextController, Configuration.pc]
  | loading acc tape =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst target
      cases acc <;> simp [nextController, Configuration.pc]

theorem encoding_length_le (config : Configuration) :
    (configurationEncoding.encode config).length ≤ 2 * config.pc + 18 * config.retained + 20 := by
  cases config with
  | «prefix» header mask challenge acc =>
      simp [configurationEncoding, fields, FiniteBitEncoding.sum, FiniteBitEncoding.prod_encode_length,
        bitList, Configuration.pc, Configuration.retained]
      omega
  | masking mask challenge acc =>
      simp [configurationEncoding, fields, FiniteBitEncoding.sum, FiniteBitEncoding.prod_encode_length,
        bitList, Configuration.pc, Configuration.retained]
      omega
  | loading acc tape =>
      have ht := ConfigurationEncoding.tape_length_le tape
      simp only [configurationEncoding, fields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        bitList, id_eq, Configuration.pc, Configuration.retained]
      omega
  | running machine =>
      have hm := ConfigurationEncoding.configuration_length_le machine
      simp only [configurationEncoding, fields, FiniteBitEncoding.sum_encode_inr_length,
        Configuration.pc, Configuration.retained]
      omega

theorem timed_eval_eq (code : Code) (start : Configuration) (fuel : Nat) :
    TimedExecution.eval (step code) fuel start = eval code start fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [TimedExecution.eval, eval_head]
      congr 1
      funext next
      exact ih next

def storageBound (code : Code) (initialPc initialRetained horizon : Nat) : Nat :=
  (codeEncoding.encode code).length + 2 * (initialPc + horizon * (code.program.addressCap + 1)) +
    18 * (initialRetained + horizon) + 20

theorem encoded_peak (code : Code) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : Configuration) (h : target ∈ (eval code start elapsed).support) :
    (codeEncoding.encode code).length + (configurationEncoding.encode target).length ≤
      storageBound code start.pc start.retained horizon := by
  rw [← timed_eval_eq] at h
  have hp := TimedExecution.ResourceGrowth.prefix_bound (step code) Configuration.pc
    (code.program.addressCap + 1) (pc_step code) horizon elapsed hElapsed start target h
  have ht := TimedExecution.ResourceGrowth.prefix_bound (step code) Configuration.retained
    1 (retained_step code) horizon elapsed hElapsed start target h
  have he := encoding_length_le target
  unfold storageBound
  omega

theorem storageBound_polynomial (code : Code) {initialPc initialRetained horizon : Nat → Nat}
    (hPc : PolynomiallyBounded initialPc) (hRetained : PolynomiallyBounded initialRetained)
    (hTime : PolynomiallyBounded horizon) :
    PolynomiallyBounded (fun n => storageBound code (initialPc n) (initialRetained n) (horizon n)) := by
  exact (((PolynomiallyBounded.const (codeEncoding.encode code).length).add
    ((PolynomiallyBounded.const 2).mul (hPc.add (hTime.mul (PolynomiallyBounded.const (code.program.addressCap + 1)))))).add
      ((PolynomiallyBounded.const 18).mul (hRetained.add hTime))).add (PolynomiallyBounded.const 20)

end Machine.Masking
