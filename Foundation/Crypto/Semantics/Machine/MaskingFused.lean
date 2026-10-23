import Foundation.Crypto.Semantics.Machine.Masking

/-! A finite-control improvement to the actual PRG masking machine. On the
last loaded cell, write the cell and transfer control directly to the native
program. This removes one empty dispatch transition. No header cell, XOR,
loading operation, or native random step is skipped. Nonempty prepared input
is required; the PRG header always satisfies this condition. -/
namespace Machine.Masking.Fused
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

noncomputable def step (code : Code) : Configuration → PMF Configuration
  | .loading [bit] tape => PMF.pure (.running { inputTape := prepend bit tape })
  | config => Masking.step code config

noncomputable def eval (code : Code) (start : Configuration) : Nat → PMF Configuration
  | 0 => PMF.pure start
  | fuel + 1 => (eval code start fuel).bind (step code)

def HaltsWithin (code : Code) (start : Configuration) (time : Nat) : Prop :=
  ∀ finish ∈ (eval code start time).support, complete finish

noncomputable def output (code : Code) (start : Configuration) (time : Nat) :
    PMF (Option Bool) := (eval code start time).map result

theorem eval_add (code : Code) (start : Configuration) (first second : Nat) :
    eval code start (first + second) =
      (eval code start first).bind (fun middle => eval code middle second) := by
  induction second with
  | zero => simp [eval]
  | succ second ih => rw [Nat.add_succ, eval, ih, PMF.bind_bind]; rfl

theorem eval_one (code : Code) (start : Configuration) : eval code start 1 = step code start := by
  simp [eval]

theorem eval_head (code : Code) (start : Configuration) (rest : Nat) :
    eval code start (rest + 1) = (step code start).bind (fun next => eval code next rest) := by
  rw [show rest + 1 = 1 + rest by omega, eval_add, eval_one]

theorem prefix_eval (code : Code) (header mask challenge acc : List Bool) :
    eval code (.prefix header mask challenge acc) (header.length + 1) =
      PMF.pure (.masking mask challenge (header.reverse ++ acc)) := by
  induction header generalizing acc with
  | nil => simp [eval, step, Masking.step, nextController]
  | cons bit rest ih =>
      rw [List.length_cons, eval_head]
      simp only [step, Masking.step, nextController, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Only equal-length masks are admitted by the cryptographic interface. -/
theorem masking_eval (code : Code) (mask challenge acc : List Bool)
    (equalLength : mask.length = challenge.length) :
    eval code (.masking mask challenge acc) (mask.length + 1) =
      PMF.pure (.loading ((xorList mask challenge).reverse ++ acc) {}) := by
  induction mask generalizing challenge acc with
  | nil =>
      have : challenge = [] := List.length_eq_zero_iff.mp equalLength.symm
      subst challenge
      simp [eval, step, Masking.step, nextController, xorList]
  | cons bit rest ih =>
      cases challenge with
      | nil => simp at equalLength
      | cons pad pads =>
          rw [List.length_cons, eval_head]
          simp only [step, Masking.step, nextController, PMF.pure_bind]
          rw [ih pads (Bool.xor bit pad :: acc) (by simpa using equalLength)]
          simp [xorList, List.reverse_cons, List.append_assoc]

theorem loading_eval (code : Code) (acc rest : List Bool) (h : 0 < acc.length) :
    eval code (.loading acc (Tape.ofBits rest)) acc.length =
      PMF.pure (.running (Machine.Configuration.initial (acc.reverse ++ rest))) := by
  induction acc generalizing rest with
  | nil => simp at h
  | cons bit tail ih =>
      cases tail with
      | nil => simp [eval, step, prepend_ofBits, Machine.Configuration.initial]
      | cons next tail =>
          rw [List.length_cons, eval_head]
          simp only [step, Masking.step, nextController, PMF.pure_bind, prepend_ofBits]
          rw [ih (bit :: rest) (by simp)]
          simp [List.reverse_cons, List.append_assoc]

/-- One final phase dispatch is fused into the last cell-loading step. -/
def overhead (headerLength messageLength : Nat) : Nat := 2 * (headerLength + messageLength) + 2

theorem masked_prepare (side : Bool) (p : Program) (header left right challenge : List Bool)
    (hNonempty : 0 < header.length + challenge.length)
    (hl : left.length = challenge.length) (hr : right.length = challenge.length) :
    eval (.masked side p) (initial (.masked side p) header left right challenge)
      (overhead header.length challenge.length) =
    PMF.pure (.running (Machine.Configuration.initial
      (header ++ xorList (if side then right else left) challenge))) := by
  have hm : (if side then right else left).length = challenge.length := by
    cases side <;> assumption
  let mask := if side then right else left
  have hsize : overhead header.length challenge.length =
      (header.length + 1) + (mask.length + 1) +
        ((xorList mask challenge).reverse ++ header.reverse).length := by
    have hml : mask.length = challenge.length := hm
    have hx := length_xorList mask challenge hm
    simp only [List.length_append, List.length_reverse]
    dsimp only [overhead]
    omega
  rw [hsize, eval_add, eval_add]
  change ((eval _ (.prefix header mask challenge []) _).bind _).bind _ = _
  rw [prefix_eval]
  simp only [List.append_nil, PMF.pure_bind]
  rw [masking_eval _ _ _ _ hm, PMF.pure_bind]
  change eval _ (.loading _ (Tape.ofBits [])) _ = _
  have hLoad : 0 < ((xorList mask challenge).reverse ++ header.reverse).length := by
    rw [List.length_append, List.length_reverse, List.length_reverse, length_xorList _ _ hm]
    have hml : mask.length = challenge.length := hm
    omega
  rw [loading_eval _ ((xorList mask challenge).reverse ++ header.reverse) [] hLoad]
  simp [List.reverse_append, mask]

/-- After preparation the caller's original native probabilistic code is
executed unchanged, retaining every branch of its fresh random bits. -/
theorem running_eval (code : Code) (machine : Machine.Configuration) (time : Nat) :
    eval code (.running machine) time =
      (evalConfigWithin code.program machine time).map Configuration.running := by
  induction time with
  | zero => simp [eval, evalConfigWithin, PMF.pure_map]
  | succ time ih =>
      rw [eval, ih, PMF.bind_map]
      simp only [Function.comp_def, step, Masking.step]
      rw [← PMF.map_bind]
      rfl

/-- Exact simulation, not merely equal final guessing probabilities. -/
theorem masked_eval (side : Bool) (p : Program) (header left right challenge : List Bool)
    (hNonempty : 0 < header.length + challenge.length)
    (hl : left.length = challenge.length) (hr : right.length = challenge.length) (time : Nat) :
    eval (.masked side p) (initial (.masked side p) header left right challenge)
      (overhead header.length challenge.length + time) =
    eval (.native p) (initial (.native p) header left right
      (xorList (if side then right else left) challenge)) time := by
  rw [eval_add, masked_prepare side p header left right challenge hNonempty hl hr, PMF.pure_bind]
  rw [running_eval]
  change _ = eval (.native p) (.running _) time
  rw [running_eval]
  rfl


def simulateStep (code : Code) (coin : Bool) : Configuration → Configuration
  | .loading [bit] tape => .running { inputTape := prepend bit tape }
  | config => Masking.simulateStep code coin config

theorem simulateStep_mem_support (code : Code) (coin : Bool) (config : Configuration) :
    simulateStep code coin config ∈ (step code config).support := by
  cases config with
  | «prefix» header mask challenge acc =>
      exact Masking.simulateStep_mem_support code coin (.prefix header mask challenge acc)
  | masking mask challenge acc =>
      exact Masking.simulateStep_mem_support code coin (.masking mask challenge acc)
  | running machine => exact Masking.simulateStep_mem_support code coin (.running machine)
  | loading acc tape =>
      cases acc with
      | nil => exact Masking.simulateStep_mem_support code coin (.loading [] tape)
      | cons bit tail =>
          cases tail with
          | nil => simp [simulateStep, step]
          | cons next rest =>
              exact Masking.simulateStep_mem_support code coin (.loading (bit :: next :: rest) tape)

def simulateLoop (code : Code) (coin : Bool) : Nat → Configuration → Nat → Configuration × Nat
  | 0, config, used => (config, used)
  | fuel + 1, config, used =>
      if (result config).isSome then (config, used) else
        simulateLoop code coin fuel (simulateStep code coin config) (used + 1)

def simulate (code : Code) (coin : Bool) (fuel : Nat) (start : Configuration) : Configuration × Nat :=
  simulateLoop code coin fuel start 0

end Machine.Masking.Fused
