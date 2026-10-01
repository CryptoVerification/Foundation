import Foundation.Machine.Basic

namespace Machine

open Foundation.Probability

/-- Exactly `steps` operational transitions along one possible sequence of
random choices. A halted configuration has no outgoing `Step`. -/
inductive RunsFor (p : Program) : Configuration → Configuration → Nat → Prop where
  | zero (c : Configuration) : RunsFor p c c 0
  | succ {c d e : Configuration} {steps : Nat}
      (prior : RunsFor p c d steps) (last : Step p d e) :
      RunsFor p c e (steps + 1)

/-- Lift a one-cell right-reading invariant through an actual trace. This
tracks retained input cells, including internal blanks, without replacing
the tape by a newly parsed or reconstructed bitstring. -/
theorem RunsFor.input_right_suffix_of_step {p : Program}
    {start finish : Configuration} {used : Nat} (run : RunsFor p start finish used)
    (hStep : ∀ c d, Step p c d →
      d.inputTape.right = c.inputTape.right ∨ d.inputTape.right = c.inputTape.right.tail) :
    ∃ count, finish.inputTape.right = start.inputTape.right.drop count := by
  induction run with
  | zero => exact ⟨0, rfl⟩
  | @succ middle finish steps prior last ih =>
      obtain ⟨count, hRight⟩ := ih
      rcases hStep middle finish last with hSame | hTail
      · exact ⟨count, hSame.trans hRight⟩
      · refine ⟨count + 1, ?_⟩
        rw [hTail, hRight, ← List.drop_one, List.drop_drop]

/-- Track the whole retained input tape through instructions that only
leave its head in place or move it one cell right. At most one such move is
charged per operational transition. This includes the saved left cells and
the current cell, not just a suffix of the represented right side. -/
theorem RunsFor.input_moveRight_of_step {p : Program}
    {start finish : Configuration} {used : Nat} (run : RunsFor p start finish used)
    (hStep : ∀ c d, Step p c d →
      d.inputTape = c.inputTape ∨ d.inputTape = c.inputTape.moveRight) :
    ∃ moves, moves ≤ used ∧ finish.inputTape = (Tape.moveRight^[moves]) start.inputTape := by
  induction run with
  | zero => exact ⟨0, Nat.le_refl _, rfl⟩
  | @succ middle finish steps prior last ih =>
      obtain ⟨moves, hMoves, hInput⟩ := ih
      rcases hStep middle finish last with hSame | hRight
      · exact ⟨moves, by omega, hSame.trans hInput⟩
      · refine ⟨moves + 1, by omega, ?_⟩
        rw [hRight, hInput, Function.iterate_succ_apply']

/-- Concatenate two actual machine traces. Their transition counts add;
this does not insert bookkeeping steps after a halt. -/
theorem RunsFor.trans {p : Program} {start middle finish : Configuration}
    {first second : Nat}
    (left : RunsFor p start middle first)
    (right : RunsFor p middle finish second) :
    RunsFor p start finish (first + second) := by
  induction right with
  | zero => simpa using left
  | succ prior last ih =>
      simpa [Nat.add_assoc] using RunsFor.succ ih last

/-- A positive-length trace has a first actual transition and a remaining
trace. This is independent of whether that transition uses a random bit. -/
theorem RunsFor.head {p : Program} {start finish : Configuration}
    {steps : Nat} (run : RunsFor p start finish (steps + 1)) :
    ∃ middle, Step p start middle ∧ RunsFor p middle finish steps := by
  induction steps generalizing finish with
  | zero =>
      cases run with
      | succ prior last =>
          cases prior with
          | zero => exact ⟨finish, last, RunsFor.zero _⟩
  | succ steps ih =>
      cases run with
      | succ prior last =>
          obtain ⟨middle, first, rest⟩ := ih prior
          exact ⟨middle, first, RunsFor.succ rest last⟩

/-- An already halted state admits only the zero-transition actual trace. -/
theorem RunsFor.eq_of_halted_start {p : Program}
    {start finish : Configuration} {steps : Nat}
    (run : RunsFor p start finish steps) (halted : start.halted = true) :
    steps = 0 ∧ finish = start := by
  induction run with
  | zero => exact ⟨rfl, rfl⟩
  | succ prior last ih =>
      rcases ih with ⟨rfl, rfl⟩
      exact False.elim ((no_step_of_halted halted) last)

/-- The program reaches this exact finite output after this exact number of
machine transitions. The final transition into `halted = true` is counted. -/
def HaltsWith (p : Program) (input output : List Bool) (steps : Nat) : Prop :=
  ∃ c, RunsFor p (Configuration.initial input) c steps ∧
    c.halted = true ∧ c.outputBits = output

/-- One real step, or a bookkeeping stutter after halting. Stuttering allows
all branches to be inspected at a common time bound without inventing extra
operational steps in `RunsFor`. -/
def PaddedStep (p : Program) (c d : Configuration) : Prop :=
  Step p c d ∨ (c.halted = true ∧ d = c)

inductive PaddedRunsFor (p : Program) : Configuration → Configuration → Nat → Prop where
  | zero (c : Configuration) : PaddedRunsFor p c c 0
  | succ {c d e : Configuration} {steps : Nat}
      (prior : PaddedRunsFor p c d steps) (last : PaddedStep p d e) :
      PaddedRunsFor p c e (steps + 1)

/-- Concatenate branch traces inspected at common time bounds. Stutters
after halt remain bookkeeping, rather than additional operational steps. -/
theorem PaddedRunsFor.trans {p : Program} {start middle finish : Configuration}
    {first second : Nat} (left : PaddedRunsFor p start middle first)
    (right : PaddedRunsFor p middle finish second) :
    PaddedRunsFor p start finish (first + second) := by
  induction right with
  | zero => simpa using left
  | succ prior last ih => simpa [Nat.add_assoc] using PaddedRunsFor.succ ih last

/-- An actual trace is also a padded trace, with no stutters added. -/
theorem RunsFor.toPadded {p : Program} {start finish : Configuration}
    {steps : Nat} (run : RunsFor p start finish steps) :
    PaddedRunsFor p start finish steps := by
  induction run with
  | zero => exact PaddedRunsFor.zero _
  | succ prior last ih => exact PaddedRunsFor.succ ih (Or.inl last)

/-- A padded trace ending before halt contains no bookkeeping stutters.
Its entire length therefore counts actual operational transitions. -/
theorem PaddedRunsFor.toRunsFor_of_running {p : Program}
    {start finish : Configuration} {steps : Nat}
    (run : PaddedRunsFor p start finish steps) (hRunning : finish.halted = false) :
    RunsFor p start finish steps := by
  induction run with
  | zero => exact RunsFor.zero _
  | @succ middle finish steps prior last ih =>
      rcases last with step | ⟨hHalted, rfl⟩
      · have hMiddle : middle.halted = false := by
          cases hh : middle.halted with
          | false => rfl
          | true => exact False.elim ((no_step_of_halted hh) step)
        exact RunsFor.succ (ih hMiddle) step
      · simp [hRunning] at hHalted

/-- Remove only post-halt bookkeeping stutters from a padded branch.
The retained trace uses actual transitions and reaches the same physical
configuration within the original inspected bound. -/
theorem PaddedRunsFor.toRunsFor_le {p : Program}
    {start finish : Configuration} {steps : Nat}
    (run : PaddedRunsFor p start finish steps) :
    ∃ used, used ≤ steps ∧ RunsFor p start finish used := by
  induction run with
  | zero => exact ⟨0, Nat.le_refl _, RunsFor.zero _⟩
  | succ prior last ih =>
      obtain ⟨used, hUsed, actual⟩ := ih
      rcases last with step | ⟨_hHalted, rfl⟩
      · exact ⟨used + 1, by omega, RunsFor.succ actual step⟩
      · exact ⟨used, by omega, actual⟩

/-- Output-tape storage grows by at most one cell per real transition;
bookkeeping stutters after halt do not grow it. -/
theorem PaddedRunsFor.outputTape_cells_le {p : Program}
    {start finish : Configuration} {steps : Nat}
    (run : PaddedRunsFor p start finish steps) :
    finish.outputTape.cells ≤ start.outputTape.cells + steps := by
  induction run with
  | zero => simp
  | succ prior last ih =>
      rcases last with hStep | ⟨_, hEq⟩
      · have hGrowth := outputTape_cells_le_of_step hStep
        omega
      · subst_vars
        omega

/-- Every possible output after `steps` transitions has at most
`steps + 1` bits. The bound includes a harmless one-cell margin. -/
theorem outputBits_length_le_of_paddedRun (p : Program)
    (input : List Bool) {finish : Configuration} {steps : Nat}
    (run : PaddedRunsFor p (Configuration.initial input) finish steps) :
    finish.outputBits.length ≤ steps + 1 := by
  have hCells := run.outputTape_cells_le
  have hBits := Tape.bits_length_le_cells finish.outputTape
  simp only [Configuration.outputBits] at hBits ⊢
  have hInitial : (Configuration.initial input).outputTape.cells = 1 := rfl
  omega

/-- All random branches have halted by `bound`: every branch padded to that
time ends in a halted configuration. The quantifier is universal. -/
def HaltsWithin (p : Program) (input : List Bool) (bound : Nat) : Prop :=
  ∀ c, PaddedRunsFor p (Configuration.initial input) c bound → c.halted = true

/-- One explicit halt instruction finishes on every input after one step. -/
theorem haltInstruction_haltsWithin (input : List Bool) :
    HaltsWithin [.halt] input 1 := by
  intro c h
  cases h with
  | succ hprior hlast =>
      cases hprior with
      | zero =>
          rcases hlast with hstep | hstop
          · have hc : c =
                { (Configuration.initial input) with halted := true } := by
              simpa [Step, successors, next, Configuration.initial,
                Instruction.next] using hstep
            rw [hc]
          · simp [Configuration.initial] at hstop

/-- Finite enumeration of all possible successors, with a halted state kept
for bookkeeping at later time bounds. This is a proof aid, not a machine
instruction and not the probabilistic evaluator. -/
def paddedSuccessors (p : Program) (c : Configuration) : List Configuration :=
  if c.halted then [c] else successors p c

theorem mem_paddedSuccessors_iff (p : Program) (c d : Configuration) :
    d ∈ paddedSuccessors p c ↔ PaddedStep p c d := by
  cases h : c.halted with
  | false => simp [paddedSuccessors, PaddedStep, h, Step]
  | true => simp [paddedSuccessors, PaddedStep, h, no_step_of_halted h]

def reachableStates (p : Program) (start : Configuration) :
    Nat → List Configuration
  | 0 => [start]
  | steps + 1 =>
      (reachableStates p start steps).flatMap (paddedSuccessors p)

theorem mem_reachableStates_iff (p : Program) (start finish : Configuration)
    (steps : Nat) :
    finish ∈ reachableStates p start steps ↔
      PaddedRunsFor p start finish steps := by
  induction steps generalizing finish with
  | zero =>
      constructor
      · intro h
        have heq : finish = start := by simpa [reachableStates] using h
        subst finish
        exact PaddedRunsFor.zero start
      · intro h
        cases h with
        | zero => simp [reachableStates]
  | succ steps ih =>
      rw [reachableStates, List.mem_flatMap]
      constructor
      · rintro ⟨middle, hmiddle, hlast⟩
        exact PaddedRunsFor.succ ((ih middle).mp hmiddle)
          ((mem_paddedSuccessors_iff p middle finish).mp hlast)
      · intro h
        cases h with
        | succ prior last =>
            exact ⟨_, (ih _).mpr prior,
              (mem_paddedSuccessors_iff p _ _).mpr last⟩

theorem haltsWithin_iff_reachableStates (p : Program) (input : List Bool)
    (bound : Nat) :
    HaltsWithin p input bound ↔
      ∀ c ∈ reachableStates p (Configuration.initial input) bound,
        c.halted = true := by
  constructor
  · intro h c hc
    exact h c ((mem_reachableStates_iff p _ c bound).mp hc)
  · intro h c hc
    exact h c ((mem_reachableStates_iff p _ c bound).mpr hc)

theorem paddedSuccessors_append_halt (p : Program) (c : Configuration) :
    paddedSuccessors (p ++ [.halt]) c = paddedSuccessors p c := by
  simp [paddedSuccessors, successors_append_halt]

theorem reachableStates_append_halt (p : Program) (start : Configuration)
    (steps : Nat) :
    reachableStates (p ++ [.halt]) start steps = reachableStates p start steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [reachableStates, ih]
      congr 1
      funext c
      exact paddedSuccessors_append_halt p c

theorem haltsWithin_append_halt_iff (p : Program) (input : List Bool)
    (bound : Nat) :
    HaltsWithin (p ++ [.halt]) input bound ↔ HaltsWithin p input bound := by
  rw [haltsWithin_iff_reachableStates, haltsWithin_iff_reachableStates,
    reachableStates_append_halt]

private theorem randomStep_support {α : Type*} (d₀ d₁ d : α) :
    d ∈ (sampleBit.map (fun b => if b then d₁ else d₀)).support ↔
      d = d₀ ∨ d = d₁ := by
  rw [PMF.mem_support_map_iff]
  constructor
  · rintro ⟨b, _, rfl⟩
    cases b <;> simp
  · rintro (rfl | rfl)
    · exact ⟨false, PMF.mem_support_uniformOfFintype false, rfl⟩
    · exact ⟨true, PMF.mem_support_uniformOfFintype true, rfl⟩

/-- The PMF has exactly the operational successors, with one added absorbing
stutter after halt. Thus no possible fair-coin branch is omitted by support. -/
theorem mem_support_stepPMF_iff (p : Program) (c d : Configuration) :
    d ∈ (stepPMF p c).support ↔ PaddedStep p c d := by
  cases hnext : next p c with
  | none =>
      have hc : c.halted = true := by
        cases h : c.halted with
        | false => simp [next, h] at hnext
        | true => rfl
      simp [stepPMF, PaddedStep, Step, successors, hnext, hc]
  | some result =>
      have hc : c.halted = false := by
        cases h : c.halted with
        | false => rfl
        | true => simp [next, h] at hnext
      cases result with
      | inl target =>
          simp [stepPMF, PaddedStep, Step, successors, hnext, hc]
      | inr pair =>
          rcases pair with ⟨d₀, d₁⟩
          rw [show stepPMF p c = sampleBit.map (fun b => if b then d₁ else d₀) by
            simp [stepPMF, hnext]]
          change _ ↔ (d ∈ successors p c) ∨ (c.halted = true ∧ d = c)
          rw [show successors p c = [d₀, d₁] by simp [successors, hnext]]
          rw [randomStep_support]
          simp [hc, eq_comm]

/-- Iterate the one-step PMF. Absorbing probability semantics after halt does
not change the exact operational transition count of `RunsFor`. -/
noncomputable def evalConfigWithin (p : Program) (c : Configuration) :
    Nat → ProbComp Configuration
  | 0 => PMF.pure c
  | steps + 1 => (evalConfigWithin p c steps).bind (stepPMF p)

/-- Split a fixed transition budget at an intermediate configuration.
This is composition of execution of the same code; it introduces neither
free tape preparation nor an extra source of randomness. -/
theorem evalConfigWithin_add (p : Program) (start : Configuration)
    (first second : Nat) :
    evalConfigWithin p start (first + second) =
      (evalConfigWithin p start first).bind
        (fun middle => evalConfigWithin p middle second) := by
  induction second with
  | zero => simp [evalConfigWithin]
  | succ second ih =>
      rw [Nat.add_succ, evalConfigWithin, ih, PMF.bind_bind]
      rfl

/-- Only the executed address needs to exclude `randomBit` for this
transition to have a point-mass distribution. Random instructions in
unvisited caller code impose no restriction. -/
theorem stepPMF_eq_pure_of_not_randomBit_at {p : Program}
    {c d : Configuration} (hStep : Step p c d) :
    (∀ tape, p[c.pc]? ≠ some (.randomBit tape)) →
    stepPMF p c = PMF.pure d := by
  intro hNoRandom
  have hactive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) hStep)
  have hNext : ∃ target, next p c = some (.inl target) := by
    cases hi : p[c.pc]? with
    | none => simp [next, hactive, hi]
    | some i =>
        cases i <;> try simp [next, hactive, hi, Instruction.next]
        exact False.elim (hNoRandom _ hi)
  obtain ⟨target, hTarget⟩ := hNext
  have hEq : d = target := by simpa [Step, successors, hTarget] using hStep
  simp [stepPMF, hTarget, hEq]

/-- A program with no random-bit opcode has a pure one-step distribution
along every actual transition. No assumption about termination is needed. -/
theorem stepPMF_eq_pure_of_no_randomBit {p : Program}
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ p)
    {c d : Configuration} (hStep : Step p c d) :
    stepPMF p c = PMF.pure d := by
  apply stepPMF_eq_pure_of_not_randomBit_at hStep
  intro tape hCode
  exact hNoRandom tape (List.mem_of_getElem? hCode)

/-- Exact operational traces of deterministic code also give exact PMF
evaluation. This lemma counts real transitions; it adds no halt padding. -/
theorem RunsFor.evalConfigWithin_eq_pure_of_no_randomBit {p : Program}
    {start finish : Configuration} {steps : Nat}
    (run : RunsFor p start finish steps)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ p) :
    evalConfigWithin p start steps = PMF.pure finish := by
  induction run with
  | zero => rfl
  | succ prior last ih =>
      simp only [evalConfigWithin, ih, PMF.pure_bind]
      exact stepPMF_eq_pure_of_no_randomBit hNoRandom last

theorem evalConfigWithin_append_halt (p : Program) (start : Configuration)
    (steps : Nat) :
    evalConfigWithin (p ++ [.halt]) start steps =
      evalConfigWithin p start steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [evalConfigWithin, ih]
      congr 1
      funext c
      exact stepPMF_append_halt p c

/-- PMF support is exactly the set of possible padded operational branches.
Random alternatives are therefore both covered by `HaltsWithin`. -/
theorem mem_support_evalConfigWithin_iff (p : Program)
    (start finish : Configuration) (steps : Nat) :
    finish ∈ (evalConfigWithin p start steps).support ↔
      PaddedRunsFor p start finish steps := by
  induction steps generalizing finish with
  | zero =>
      constructor
      · intro h
        have heq : finish = start := by
          simpa [evalConfigWithin] using h
        subst finish
        exact PaddedRunsFor.zero start
      · intro h
        cases h with
        | zero => simp [evalConfigWithin]
  | succ steps ih =>
      rw [evalConfigWithin, PMF.mem_support_bind_iff]
      constructor
      · rintro ⟨middle, hmiddle, hlast⟩
        exact PaddedRunsFor.succ ((ih middle).mp hmiddle)
          ((mem_support_stepPMF_iff p middle finish).mp hlast)
      · intro h
        cases h with
        | succ prior last =>
            exact ⟨_, (ih _).mpr prior,
              (mem_support_stepPMF_iff p _ _).mpr last⟩

/-- The output distribution after a fixed number of machine steps. `none`
records a branch that has not halted within the supplied fuel. -/
noncomputable def evalWithin (p : Program) (input : List Bool) (fuel : Nat) :
    ProbComp (Option (List Bool)) :=
  (evalConfigWithin p (Configuration.initial input) fuel).map fun c =>
    if c.halted then some c.outputBits else none

/-- A halted trace of code without random-bit instructions determines the
entire output distribution at that exact transition count. -/
theorem HaltsWith.evalWithin_eq_pure_of_no_randomBit {p : Program}
    {input output : List Bool} {steps : Nat}
    (halts : HaltsWith p input output steps)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ p) :
    evalWithin p input steps = PMF.pure (some output) := by
  obtain ⟨finish, run, hHalted, hOutput⟩ := halts
  have hEval := run.evalConfigWithin_eq_pure_of_no_randomBit hNoRandom
  simp [evalWithin, hEval, PMF.pure_map, hHalted, hOutput]

theorem evalWithin_append_halt (p : Program) (input : List Bool)
    (fuel : Nat) :
    evalWithin (p ++ [.halt]) input fuel = evalWithin p input fuel := by
  unfold evalWithin
  rw [evalConfigWithin_append_halt]

/-- Any bitstring emitted with positive probability fits in the number of
machine transitions (with the one-cell margin from the tape representation). -/
theorem evalWithin_output_length_le (p : Program) (input : List Bool)
    (fuel : Nat) (bits : List Bool)
    (h : some bits ∈ (evalWithin p input fuel).support) :
    bits.length ≤ fuel + 1 := by
  change some bits ∈ ((evalConfigWithin p (Configuration.initial input) fuel).map
    (fun c => if c.halted then some c.outputBits else none)).support at h
  rw [PMF.mem_support_map_iff] at h
  rcases h with ⟨c, hc, hOutput⟩
  cases hHalted : c.halted with
  | false => simp [hHalted] at hOutput
  | true =>
      have hRun := (mem_support_evalConfigWithin_iff p _ c fuel).mp hc
      have hLength := outputBits_length_le_of_paddedRun p input hRun
      simp only [hHalted, ↓reduceIte, Option.some.injEq] at hOutput
      simpa [← hOutput] using hLength

/-- A universal halting bound excludes timeout from the evaluator's support
and hence gives timeout probability zero. -/
theorem evalWithin_no_timeout (p : Program) (input : List Bool) (fuel : Nat)
    (h : HaltsWithin p input fuel) :
    eventProb (evalWithin p input fuel) (· = none) = 0 := by
  have hNone : none ∉ (evalWithin p input fuel).support := by
    intro hSupport
    change none ∈ ((evalConfigWithin p (Configuration.initial input) fuel).map
      (fun c => if c.halted then some c.outputBits else none)).support at hSupport
    rw [PMF.mem_support_map_iff] at hSupport
    rcases hSupport with ⟨c, hc, hOutput⟩
    have hHalted : c.halted = true :=
      h c ((mem_support_evalConfigWithin_iff p _ c fuel).mp hc)
    simp [hHalted] at hOutput
  change (evalWithin p input fuel).toOuterMeasure {none} = 0
  rw [PMF.toOuterMeasure_apply_singleton]
  exact ((evalWithin p input fuel).apply_eq_zero_iff none).2 hNone

/-- Conversely, absence of timeout in PMF support proves the universal
operational bound, because every padded branch occurs in that support. -/
theorem haltsWithin_of_no_timeout_support (p : Program) (input : List Bool)
    (fuel : Nat) (hNone : none ∉ (evalWithin p input fuel).support) :
    HaltsWithin p input fuel := by
  intro c hRun
  cases hHalted : c.halted with
  | true => rfl
  | false =>
      have hc : c ∈ (evalConfigWithin p (Configuration.initial input) fuel).support :=
        (mem_support_evalConfigWithin_iff p _ c fuel).2 hRun
      have hOutput : none ∈ (evalWithin p input fuel).support := by
        change none ∈ ((evalConfigWithin p (Configuration.initial input) fuel).map
          (fun d => if d.halted then some d.outputBits else none)).support
        rw [PMF.mem_support_map_iff]
        exact ⟨c, hc, by simp [hHalted]⟩
      exact False.elim (hNone hOutput)

/-- For deterministic code, one halted actual trace proves the universal
halting bound. Randomized code cannot use this implication without the
explicit absence-of-random-instructions hypothesis. -/
theorem HaltsWith.haltsWithin_of_no_randomBit {p : Program}
    {input output : List Bool} {steps : Nat}
    (halts : HaltsWith p input output steps)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ p) :
    HaltsWithin p input steps := by
  apply haltsWithin_of_no_timeout_support
  rw [halts.evalWithin_eq_pure_of_no_randomBit hNoRandom]
  simp

/-- A larger common budget preserves the complete distribution from an
arbitrary retained configuration after every native branch has halted. This
does not reload the tapes or discard their physical blank representation. -/
theorem evalConfigWithin_eq_of_le (p : Program) (start : Configuration)
    (fuel budget : Nat) (hLe : fuel ≤ budget)
    (h : ∀ c, PaddedRunsFor p start c fuel → c.halted = true) :
    evalConfigWithin p start budget = evalConfigWithin p start fuel := by
  have haltedEval (c : Configuration) (hc : c.halted = true) (extra : Nat) :
      evalConfigWithin p c extra = PMF.pure c := by
    induction extra with
    | zero => rfl
    | succ extra ih => simp [evalConfigWithin, ih, stepPMF, next, hc]
  rw [show budget = fuel + (budget - fuel) by omega, evalConfigWithin_add]
  rw [← PMF.bindOnSupport_eq_bind]
  calc
    _ = (evalConfigWithin p start fuel).bindOnSupport (fun c _ => PMF.pure c) := by
      congr 1
      funext c hc
      exact haltedEval c (h c ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)) _
    _ = _ := PMF.bindOnSupport_pure _

/-- A halted actual trace of deterministic code certifies every padded
branch at any larger common budget, from the same retained configuration.
This transfers native stopping certificates to probabilistic composition
without resetting tapes or charging artificial execution steps. -/
theorem RunsFor.haltsFrom_of_no_randomBit {p : Program} {start target : Configuration}
    {used budget : Nat} (run : RunsFor p start target used)
    (hHalted : target.halted = true)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ p)
    (hBound : used ≤ budget) :
    ∀ finish, PaddedRunsFor p start finish budget → finish.halted = true := by
  have hEval := run.evalConfigWithin_eq_pure_of_no_randomBit hNoRandom
  have hAt (c : Configuration) (hc : PaddedRunsFor p start c used) : c.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr hc
    rw [hEval, PMF.mem_support_pure_iff] at hMem
    simpa only [hMem] using hHalted
  intro finish trace
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt, hEval, PMF.mem_support_pure_iff] at hMem
  simpa only [hMem] using hHalted

/-- Two halted traces of deterministic code from the same retained
configuration have the same final configuration, even if their transition
counts differ. No tape cells are reset or reconstructed by this theorem. -/
theorem RunsFor.halted_finish_eq_of_no_randomBit {p : Program} {start first second : Configuration}
    {firstTime secondTime : Nat}
    (hFirst : RunsFor p start first firstTime) (hSecond : RunsFor p start second secondTime)
    (hFirstHalt : first.halted = true) (hSecondHalt : second.halted = true)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ p) : first = second := by
  have hAt (finish : Configuration) (used bound : Nat)
      (run : RunsFor p start finish used) (hHalted : finish.halted = true) (hLe : used ≤ bound) :
      evalConfigWithin p start bound = PMF.pure finish := by
    have hEval := run.evalConfigWithin_eq_pure_of_no_randomBit hNoRandom
    have hAll (target : Configuration) (trace : PaddedRunsFor p start target used) : target.halted = true := by
      have hMem := (mem_support_evalConfigWithin_iff p start target used).mpr trace
      rw [hEval] at hMem
      have hEq : target = finish := by simpa using hMem
      simpa only [hEq] using hHalted
    exact (evalConfigWithin_eq_of_le p start used bound hLe hAll).trans hEval
  have hEqual : PMF.pure first = PMF.pure second :=
    (hAt first firstTime (max firstTime secondTime) hFirst hFirstHalt (Nat.le_max_left _ _)).symm.trans
      (hAt second secondTime (max firstTime secondTime) hSecond hSecondHalt (Nat.le_max_right _ _))
  have hMem : first ∈ (PMF.pure second).support := by rw [← hEqual]; simp
  simpa using hMem

/-- Once every branch has halted, further probabilistic evaluation steps
leave the configuration distribution unchanged. -/
theorem evalConfigWithin_stable (p : Program) (input : List Bool)
    (fuel extra : Nat) (h : HaltsWithin p input fuel) :
    evalConfigWithin p (Configuration.initial input) (fuel + extra) =
      evalConfigWithin p (Configuration.initial input) fuel := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ, evalConfigWithin]
      have hStep : ∀ c ∈
          (evalConfigWithin p (Configuration.initial input) (fuel + extra)).support,
          stepPMF p c = PMF.pure c := by
        intro c hc
        rw [ih] at hc
        have hcHalted : c.halted = true :=
          h c ((mem_support_evalConfigWithin_iff p _ c fuel).mp hc)
        simp [stepPMF, next, hcHalted]
      rw [← PMF.bindOnSupport_eq_bind]
      calc
        (evalConfigWithin p (Configuration.initial input) (fuel + extra)).bindOnSupport
            (fun c _ => stepPMF p c) =
          (evalConfigWithin p (Configuration.initial input) (fuel + extra)).bindOnSupport
            (fun c _ => PMF.pure c) := by
              congr 1
              funext c hc
              exact hStep c hc
        _ = evalConfigWithin p (Configuration.initial input) (fuel + extra) :=
          PMF.bindOnSupport_pure _
        _ = evalConfigWithin p (Configuration.initial input) fuel := ih

theorem evalWithin_stable (p : Program) (input : List Bool)
    (fuel extra : Nat) (h : HaltsWithin p input fuel) :
    evalWithin p input (fuel + extra) = evalWithin p input fuel := by
  unfold evalWithin
  rw [evalConfigWithin_stable p input fuel extra h]

/-- Any two valid all-branch stopping budgets yield the same output PMF.
The fuel is therefore analysis data rather than an advice channel. -/
theorem evalWithin_eq_of_haltsWithin (p : Program) (input : List Bool)
    (fuel₁ fuel₂ : Nat)
    (h₁ : HaltsWithin p input fuel₁)
    (h₂ : HaltsWithin p input fuel₂) :
    evalWithin p input fuel₁ = evalWithin p input fuel₂ := by
  let common := max fuel₁ fuel₂
  have hLeft : evalWithin p input common = evalWithin p input fuel₁ := by
    have := evalWithin_stable p input fuel₁ (common - fuel₁) h₁
    simpa [common, Nat.add_sub_of_le (le_max_left fuel₁ fuel₂)] using this
  have hRight : evalWithin p input common = evalWithin p input fuel₂ := by
    have := evalWithin_stable p input fuel₂ (common - fuel₂) h₂
    simpa [common, Nat.add_sub_of_le (le_max_right fuel₁ fuel₂)] using this
  exact hLeft.symm.trans hRight

/-- A larger step budget preserves a worst-case halting guarantee. Once a
branch halts, padding can only keep the same halted configuration. -/
theorem HaltsWithin.mono {p : Program} {input : List Bool} {bound bound' : Nat}
    (h : HaltsWithin p input bound) (hle : bound ≤ bound') :
    HaltsWithin p input bound' := by
  have hAdd : ∀ extra : Nat, HaltsWithin p input (bound + extra) := by
    intro extra
    induction extra with
    | zero => simpa using h
    | succ extra ih =>
        intro c hRun
        have hRun' : PaddedRunsFor p (Configuration.initial input) c
            ((bound + extra) + 1) := by
          simpa only [Nat.add_succ] using hRun
        cases hRun' with
        | succ prior last =>
            have hMiddle := ih _ prior
            rcases last with hStep | ⟨_, hEq⟩
            · exact False.elim (no_step_of_halted hMiddle hStep)
            · simpa [hEq] using hMiddle
  simpa only [Nat.add_sub_of_le hle] using hAdd (bound' - bound)

/-- A stopping certificate gives an actual halted branch within its bound.
The witness is a trace of the existing program, not newly supplied machine
code or an uncharged reset of the starting configuration. -/
theorem exists_halted_run_of_haltsFrom (p : Program) (start : Configuration) (bound : Nat)
    (halts : ∀ finish, PaddedRunsFor p start finish bound → finish.halted = true) :
    ∃ finish used, used ≤ bound ∧ RunsFor p start finish used ∧ finish.halted = true := by
  obtain ⟨finish, hMem⟩ := (evalConfigWithin p start bound).support_nonempty
  have padded := (mem_support_evalConfigWithin_iff _ _ _ _).mp hMem
  obtain ⟨used, hUsed, actual⟩ := padded.toRunsFor_le
  exact ⟨finish, used, hUsed, actual, halts finish padded⟩

end Machine
