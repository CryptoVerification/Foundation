import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoff

/-! Native private table-key generation followed by cell-by-cell rewind.
Input markers specify the key length; they are caller input data rather than
instance-dependent generated code. The random output tape is transferred to
the private key store, never to an adversary's public output. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivateKeyGeneration
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

inductive Control where
  | generating : Configuration → Control
  | rewinding : Tape → Control
  | ready : Tape → Control
  deriving DecidableEq, Repr

def readyStore : Control → Option Tape
  | .ready tape => some tape
  | _ => none

noncomputable def step : Control → PMF Control
  | .generating machine =>
      if machine.halted then PMF.pure (.rewinding machine.outputTape)
      else (stepPMF OneTimePad.Native.keygenCode machine).map .generating
  | .rewinding tape =>
      match tape.left with
      | [] => PMF.pure (.ready tape)
      | _ :: _ => PMF.pure (.rewinding tape.moveLeft)
  | .ready tape => PMF.pure (.ready tape)

noncomputable def eval : Nat → Control → PMF Control
  | 0, start => PMF.pure start
  | fuel + 1, start => (step start).bind (eval fuel)

theorem eval_add (first second : Nat) (start : Control) :
    eval (first + second) start = (eval first start).bind (eval second) := by
  induction first generalizing start with
  | zero => simp [eval, PMF.pure_bind]
  | succ first ih =>
      simp only [Nat.succ_add, eval, PMF.bind_bind]
      congr 1
      funext next
      exact ih next

theorem generating_iteration (pastInput pastKey rest : List Bool) (marker : Bool) :
    eval 5 (.generating (Machine.OneTimePad.state pastInput pastKey (marker :: rest))) =
      sampleBit.map (fun bit => .generating
        (Machine.OneTimePad.state (pastInput ++ [marker]) (pastKey ++ [bit]) rest)) := by
  cases marker <;> cases rest <;>
    simp [eval, step, stepPMF, next, OneTimePad.Native.keygenCode, Machine.OneTimePad.keygen,
      Machine.OneTimePad.state, Tape.ofBits, Instruction.next, Configuration.tape,
      Configuration.updateTape, Configuration.advance, Tape.write, Tape.moveRight,
      PMF.bind_map, PMF.map_bind, PMF.map_comp, PMF.pure_map, Function.comp_def, List.reverse_append]
  all_goals
    rw [PMF.map]
    congr 1
    funext bit
    cases bit <;>
      simp [eval, step, stepPMF, next, OneTimePad.Native.keygenCode, Machine.OneTimePad.keygen,
        Machine.OneTimePad.state, Tape.ofBits, Instruction.next, Configuration.tape,
        Configuration.updateTape, Configuration.advance, Tape.write, Tape.moveRight, PMF.pure_map, List.reverse_append]

/-- Joint distribution of both physical tapes at the actual native halt.
The controller has not yet exposed or transferred the generated key. -/
theorem generating_run (pastInput pastKey remaining : List Bool) :
    eval (5 * remaining.length + 2)
      (.generating (Machine.OneTimePad.state pastInput pastKey remaining)) =
      (uniform (Bits remaining.length)).map (fun key => .generating
        (Machine.OneTimePad.finish 5 (pastInput ++ remaining) (pastKey ++ key.toList))) := by
  induction remaining generalizing pastInput pastKey with
  | nil =>
      simp [eval, step, stepPMF, next, OneTimePad.Native.keygenCode, Machine.OneTimePad.keygen,
        Machine.OneTimePad.state, Machine.OneTimePad.finish, Tape.ofBits, Instruction.next,
        Configuration.tape, Bits.toList, PMF.map_const, PMF.pure_map]
      simpa [Function.const_def, Machine.OneTimePad.finish, Machine.OneTimePad.state, Tape.ofBits] using
        (PMF.map_const (uniform (Bits 0)) (Control.generating (Machine.OneTimePad.finish 5 pastInput pastKey))).symm
  | cons marker rest ih =>
      rw [show 5 * (marker :: rest).length + 2 = 5 + (5 * rest.length + 2) by simp; omega,
        eval_add, generating_iteration, PMF.bind_map]
      simp only [Function.comp_def, ih, List.length_cons]
      rw [← uniform_bits_cons]
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def,
        Bits.toList, List.ofFn_succ, List.append_assoc]

theorem rewind_run (left : List Bool) (current : Option Bool) (right : List (Option Bool)) :
    eval (left.length + 1) (.rewinding ⟨left.map some, current, right⟩) =
      PMF.pure (.ready (ResponseHandoff.fromCells (left.reverse.map some ++ current :: right))) := by
  induction left generalizing current right with
  | nil => simp [eval, step, ResponseHandoff.fromCells, PMF.pure_bind]
  | cons bit left ih =>
      rw [show (bit :: left).length + 1 = (left.length + 1) + 1 by rfl, eval]
      simp only [step, List.map_cons, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind_before_ready (left : List Bool) (current : Option Bool) (right : List (Option Bool)) :
    eval left.length (.rewinding ⟨left.map some, current, right⟩) =
      PMF.pure (.rewinding (ResponseHandoff.fromCells (left.reverse.map some ++ current :: right))) := by
  induction left generalizing current right with
  | nil => simp [eval, ResponseHandoff.fromCells]
  | cons bit left ih =>
      rw [List.length_cons, eval]
      simp only [step, List.map_cons, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def initial (markers : List Bool) : Control :=
  .generating (Configuration.initial markers)

/-- The complete sampler includes native generation, one ownership transfer,
one move for every generated cell, and the final ready-state transition. -/
theorem full_run (markers : List Bool) :
    eval (6 * markers.length + 4) (initial markers) =
      (uniform (Bits markers.length)).map (fun key => .ready
        (ResponseHandoff.fromCells (key.toList.map some ++ [none]))) := by
  unfold initial
  rw [← Machine.OneTimePad.state_initial,
    show 6 * markers.length + 4 = (5 * markers.length + 2) + ((markers.length + 1) + 1) by omega,
    eval_add, generating_run, PMF.bind_map]
  simp only [Function.comp_def, List.nil_append]
  rw [PMF.map]
  congr 1
  funext key
  rw [eval]
  simp only [step, Machine.OneTimePad.finish, Machine.OneTimePad.state, ↓reduceIte, PMF.pure_bind]
  have hLength : key.toList.reverse.length = markers.length := by simp
  rw [show markers.length + 1 = key.toList.reverse.length + 1 by rw [hLength], rewind_run]
  simp

theorem before_ready_run (markers : List Bool) :
    eval (6 * markers.length + 3) (initial markers) =
      (uniform (Bits markers.length)).map (fun key => .rewinding
        (ResponseHandoff.fromCells (key.toList.map some ++ [none]))) := by
  unfold initial
  rw [← Machine.OneTimePad.state_initial,
    show 6 * markers.length + 3 = (5 * markers.length + 2) + (markers.length + 1) by omega,
    eval_add, generating_run, PMF.bind_map]
  simp only [Function.comp_def, List.nil_append]
  rw [PMF.map]
  congr 1
  funext key
  rw [eval]
  simp only [step, Machine.OneTimePad.finish, Machine.OneTimePad.state, ↓reduceIte, PMF.pure_bind]
  have hLength : key.toList.reverse.length = markers.length := by simp
  conv_lhs => arg 1; rw [← hLength]
  rw [rewind_before_ready]
  simp

def store {width : Nat} (key : TableMAC.Key width) : Tape :=
  ResponseHandoff.fromCells ((ResponseHandoff.keyBytes key).map some ++ [none])

theorem generating_typed_run (width : Nat) (pastInput pastKey : List Bool) :
    eval (5 * width + 2)
      (.generating (Machine.OneTimePad.state pastInput pastKey (List.replicate width true))) =
      (uniform (Bits width)).map (fun key => .generating
        (Machine.OneTimePad.finish 5 (pastInput ++ List.replicate width true) (pastKey ++ key.toList))) := by
  induction width generalizing pastInput pastKey with
  | zero =>
      simp [eval, step, stepPMF, next, OneTimePad.Native.keygenCode, Machine.OneTimePad.keygen,
        Machine.OneTimePad.state, Machine.OneTimePad.finish, Tape.ofBits, Instruction.next,
        Configuration.tape, Bits.toList, PMF.map_const, PMF.pure_map]
      simpa [Function.const_def, Machine.OneTimePad.finish, Machine.OneTimePad.state, Tape.ofBits] using
        (PMF.map_const (uniform (Bits 0)) (Control.generating (Machine.OneTimePad.finish 5 pastInput pastKey))).symm
  | succ width ih =>
      rw [List.replicate_succ, show 5 * (width + 1) + 2 = 5 + (5 * width + 2) by omega,
        eval_add, generating_iteration, PMF.bind_map]
      simp only [Function.comp_def, ih]
      rw [← uniform_bits_cons]
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def,
        Bits.toList, List.ofFn_succ, List.replicate_succ, List.append_assoc]

theorem typed_full_run (width : Nat) :
    eval (6 * width + 4) (initial (List.replicate width true)) =
      (uniform (Bits width)).map (fun key => .ready
        (ResponseHandoff.fromCells (key.toList.map some ++ [none]))) := by
  unfold initial
  rw [← Machine.OneTimePad.state_initial,
    show 6 * width + 4 = (5 * width + 2) + ((width + 1) + 1) by omega,
    eval_add, generating_typed_run, PMF.bind_map]
  simp only [Function.comp_def, List.nil_append]
  rw [PMF.map]
  congr 1
  funext key
  rw [eval]
  simp only [step, Machine.OneTimePad.finish, Machine.OneTimePad.state, ↓reduceIte, PMF.pure_bind]
  rw [show width + 1 = key.toList.reverse.length + 1 by simp, rewind_run]
  simp

/-- The actual private sampler has exactly the independently uniform two-row
key distribution required by the semantic MAC, with its physical layout. -/
theorem table_key_run (width : Nat → Nat) (n : Nat) :
    eval (12 * width n + 4) (initial (List.replicate (2 * width n) true)) =
      ((TableMAC.scheme width).keygen n).map (fun key => .ready (store key)) := by
  rw [show 12 * width n + 4 = 6 * (2 * width n) + 4 by omega, typed_full_run]
  simp only [TableMAC.scheme, PMF.map_comp, Function.comp_def,
    store, ResponseHandoff.keyBytes, TableMAC.splitKey_encoding]

theorem store_equivalent {width : Nat} (key : TableMAC.Key width) :
    (store key).Equivalent (Tape.ofBits (ResponseHandoff.keyBytes key)) :=
  ResponseHandoff.prepared_equivalent _

def ReadyWithin (start : Control) (fuel : Nat) : Prop :=
  ∀ final ∈ (eval fuel start).support, (readyStore final).isSome = true

theorem ready_within (markers : List Bool) : ReadyWithin (initial markers) (6 * markers.length + 4) := by
  intro final hFinal
  rw [full_run, PMF.mem_support_map_iff] at hFinal
  obtain ⟨key, _, hEq⟩ := hFinal
  subst final
  rfl

theorem not_ready_before (markers : List Bool) : ¬ ReadyWithin (initial markers) (6 * markers.length + 3) := by
  intro h
  let key : Bits markers.length := fun _ => false
  have hm : Control.rewinding (ResponseHandoff.fromCells (key.toList.map some ++ [none])) ∈
      (eval (6 * markers.length + 3) (initial markers)).support := by
    rw [before_ready_run, PMF.mem_support_map_iff]
    exact ⟨key, by simp [uniform], rfl⟩
  have hc := h _ hm
  simp [readyStore] at hc

theorem eval_ready (fuel : Nat) (tape : Tape) : eval fuel (.ready tape) = PMF.pure (.ready tape) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [eval, step, PMF.pure_bind, ih]

theorem eval_stable (start : Control) (fuel extra : Nat) (h : ReadyWithin start fuel) :
    eval (fuel + extra) start = eval fuel start := by
  rw [eval_add, ← PMF.bindOnSupport_eq_bind]
  calc
    (eval fuel start).bindOnSupport (fun final _ => eval extra final) =
        (eval fuel start).bindOnSupport (fun final _ => PMF.pure final) := by
      congr 1
      funext final hFinal
      have hr := h final hFinal
      cases final with
      | generating _ => simp [readyStore] at hr
      | rewinding _ => simp [readyStore] at hr
      | ready tape => exact eval_ready extra tape
    _ = eval fuel start := PMF.bindOnSupport_pure _

theorem store_bits {width : Nat} (key : TableMAC.Key width) :
    (store key).bits = ResponseHandoff.keyBytes key := by
  rw [(store_equivalent key).bits]
  cases ResponseHandoff.keyBytes key <;> simp [Tape.ofBits, Tape.bits, List.filterMap_map]

def simulateStep (coin : Bool) : Control → Control
  | .generating machine =>
      if machine.halted then .rewinding machine.outputTape
      else .generating (Masking.nativeNext OneTimePad.Native.keygenCode machine coin)
  | .rewinding tape =>
      match tape.left with
      | [] => .ready tape
      | _ :: _ => .rewinding tape.moveLeft
  | .ready tape => .ready tape

private theorem native_mem_support (machine : Configuration) (coin : Bool) :
    Masking.nativeNext OneTimePad.Native.keygenCode machine coin ∈
      (stepPMF OneTimePad.Native.keygenCode machine).support := by
  have hm := Masking.simulateStep_mem_support (.native OneTimePad.Native.keygenCode) coin (.running machine)
  change Masking.Configuration.running (Masking.nativeNext OneTimePad.Native.keygenCode machine coin) ∈
    ((stepPMF OneTimePad.Native.keygenCode machine).map Masking.Configuration.running).support at hm
  rw [PMF.mem_support_map_iff] at hm
  obtain ⟨final, hFinal, hEq⟩ := hm
  have he : final = Masking.nativeNext OneTimePad.Native.keygenCode machine coin := by cases hEq; rfl
  rw [← he]
  exact hFinal

theorem simulateStep_mem_support (coin : Bool) (start : Control) :
    simulateStep coin start ∈ (step start).support := by
  cases start with
  | generating machine =>
      cases hh : machine.halted with
      | true => simp [simulateStep, step, hh]
      | false =>
          simp only [simulateStep, step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff]
          exact ⟨_, native_mem_support _ coin, rfl⟩
  | rewinding tape => cases hl : tape.left <;> simp [simulateStep, step, hl]
  | ready tape => simp [simulateStep, step]

def simulate (coin : Bool) : Nat → Control → Control × Nat
  | 0, start => (start, 0)
  | fuel + 1, start =>
      if (readyStore start).isSome then (start, 0)
      else let result := simulate coin fuel (simulateStep coin start)
           (result.1, result.2 + 1)

theorem simulate_mem_support (coin : Bool) (fuel : Nat) (start : Control) :
    (simulate coin fuel start).1 ∈ (eval fuel start).support := by
  induction fuel generalizing start with
  | zero => simp [simulate, eval]
  | succ fuel ih =>
      by_cases h : (readyStore start).isSome = true
      · cases start with
        | generating _ => simp [readyStore] at h
        | rewinding _ => simp [readyStore] at h
        | ready tape => rw [eval_ready]; simp [simulate, readyStore]
      · simp only [simulate, h, ↓reduceIte, eval, PMF.mem_support_bind_iff]
        exact ⟨simulateStep coin start, simulateStep_mem_support coin start, ih _⟩

theorem profile_polynomial {width : Nat → Nat} (h : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => 12 * width n + 4) :=
  ((PolynomiallyBounded.const 12).mul h).add (PolynomiallyBounded.const 4)

end Foundation.Symmetric.EncryptThenMAC.PrivateKeyGeneration
