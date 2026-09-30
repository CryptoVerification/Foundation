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

end Machine
