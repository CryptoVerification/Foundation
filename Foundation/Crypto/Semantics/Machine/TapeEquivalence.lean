import Foundation.Crypto.Semantics.Machine.SubroutineProbability

namespace Machine

namespace Tape

/-- Two finite zipper representations describe the same cells relative to
their heads. Unrepresented cells and represented `none` cells are both blank.
This is a proof relation, not a tape-normalization machine instruction. -/
def Equivalent (t s : Tape) : Prop :=
  t.current = s.current ∧
    (∀ i, t.left.getD i none = s.left.getD i none) ∧
    (∀ i, t.right.getD i none = s.right.getD i none)

theorem Equivalent.refl (t : Tape) : t.Equivalent t :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem Equivalent.symm {t s : Tape} (h : t.Equivalent s) : s.Equivalent t :=
  ⟨h.1.symm, fun i => (h.2.1 i).symm, fun i => (h.2.2 i).symm⟩

theorem Equivalent.trans {first middle last : Tape}
    (hFirst : first.Equivalent middle) (hLast : middle.Equivalent last) : first.Equivalent last :=
  ⟨hFirst.1.trans hLast.1, fun i => (hFirst.2.1 i).trans (hLast.2.1 i),
    fun i => (hFirst.2.2 i).trans (hLast.2.2 i)⟩

/-- Explicitly stored blank padding represents the same right-hand cells
as unrepresented blank space. This is a layout proof, not a machine action. -/
theorem blank_padding_equivalent (before : List (Option Bool)) (blanks : Nat) :
    ({ left := before, right := List.replicate blanks none } : Tape).Equivalent { left := before } := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro i
  change (List.replicate blanks (none : Option Bool)).getD i none = none
  induction blanks generalizing i with
  | zero => simp
  | succ blanks ih =>
      cases i with
      | zero => simp [List.replicate_succ]
      | succ i => simpa only [List.replicate_succ, List.getD_cons_succ] using ih i

theorem Equivalent.write {t s : Tape} (h : t.Equivalent s) (cell : Option Bool) :
    (t.write cell).Equivalent (s.write cell) :=
  ⟨rfl, h.2.1, h.2.2⟩

private theorem left_current (t : Tape) :
    t.moveLeft.current = t.left.getD 0 none := by
  cases ht : t.left <;> simp [moveLeft, ht]

private theorem left_left (t : Tape) (i : Nat) :
    t.moveLeft.left.getD i none = t.left.getD (i + 1) none := by
  cases ht : t.left <;> simp [moveLeft, ht]

private theorem left_right (t : Tape) : t.moveLeft.right = t.current :: t.right := by
  cases ht : t.left <;> simp [moveLeft, ht]

private theorem right_current (t : Tape) :
    t.moveRight.current = t.right.getD 0 none := by
  cases ht : t.right <;> simp [moveRight, ht]

private theorem right_right (t : Tape) (i : Nat) :
    t.moveRight.right.getD i none = t.right.getD (i + 1) none := by
  cases ht : t.right <;> simp [moveRight, ht]

private theorem right_left (t : Tape) : t.moveRight.left = t.current :: t.left := by
  cases ht : t.right <;> simp [moveRight, ht]

theorem Equivalent.moveLeft {t s : Tape} (h : t.Equivalent s) :
    t.moveLeft.Equivalent s.moveLeft := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [left_current] using h.2.1 0
  · intro i
    simpa only [left_left] using h.2.1 (i + 1)
  · intro i
    cases i with
    | zero => simpa only [left_right, List.getD_cons_zero] using h.1
    | succ i => simpa only [left_right, List.getD_cons_succ] using h.2.2 i

theorem Equivalent.moveRight {t s : Tape} (h : t.Equivalent s) :
    t.moveRight.Equivalent s.moveRight := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [right_current] using h.2.2 0
  · intro i
    cases i with
    | zero => simpa only [right_left, List.getD_cons_zero] using h.1
    | succ i => simpa only [right_left, List.getD_cons_succ] using h.2.1 i
  · intro i
    simpa only [right_right] using h.2.2 (i + 1)

private theorem filterMap_eq_nil_of_blank (xs : List (Option Bool))
    (h : ∀ i, xs.getD i none = none) : xs.filterMap id = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : x = none := by simpa using h 0
      have hxs : ∀ i, xs.getD i none = none := by
        intro i
        simpa using h (i + 1)
      rw [hx, List.filterMap_cons]
      exact ih hxs

private theorem filterMap_eq_of_cells (xs ys : List (Option Bool))
    (h : ∀ i, xs.getD i none = ys.getD i none) :
    xs.filterMap id = ys.filterMap id := by
  induction xs generalizing ys with
  | nil =>
      exact (filterMap_eq_nil_of_blank ys (fun i => by
        simpa using (h i).symm)).symm
  | cons x xs ih =>
      cases ys with
      | nil =>
          exact filterMap_eq_nil_of_blank (x :: xs) (fun i => by simpa using h i)
      | cons y ys =>
          have hxy : x = y := by simpa using h 0
          have hTail : ∀ i, xs.getD i none = ys.getD i none := by
            intro i
            simpa using h (i + 1)
          simp only [List.filterMap_cons]
          rw [hxy, ih ys hTail]

theorem Equivalent.bits {t s : Tape} (h : t.Equivalent s) : t.bits = s.bits := by
  have hLeft := filterMap_eq_of_cells t.left s.left h.2.1
  have hRight := filterMap_eq_of_cells t.right s.right h.2.2
  simp only [Tape.bits, List.filterMap_append, List.filterMap_reverse,
    List.filterMap_cons, hLeft, hRight, h.1]

/-- The exposed contiguous suffix cannot contain more bits than the actual
finite tape has represented cells, even if an equivalent layout retains
extra blank padding in its saved prefix. -/
theorem Equivalent.contiguous_length_le_cells {input : Tape} {bits : List Bool}
    {before : List (Option Bool)}
    (h : input.Equivalent { ofBits bits with left := before }) : bits.length ≤ input.cells := by
  have hLength : bits.length ≤ ({ ofBits bits with left := before } : Tape).bits.length := by
    cases bits <;> simp [ofBits, Tape.bits, List.filterMap_append]
  calc
    bits.length ≤ ({ ofBits bits with left := before } : Tape).bits.length := hLength
    _ = input.bits.length := congrArg List.length h.bits.symm
    _ ≤ input.cells := bits_length_le_cells input

/-- A move out into unrepresented blank space followed by its inverse may
leave a redundant blank in the finite representation, but restores all cells
relative to the head. Both moves are still actual charged transitions. -/
theorem moveLeft_moveRight_equivalent (t : Tape) :
    t.moveLeft.moveRight.Equivalent t := by
  cases t with
  | mk left current right =>
      cases left with
      | nil =>
          refine ⟨rfl, ?_, fun _ => rfl⟩
          intro i
          cases i <;> simp [moveLeft, moveRight]
      | cons cell rest => exact Equivalent.refl _

theorem moveRight_moveLeft_equivalent (t : Tape) :
    t.moveRight.moveLeft.Equivalent t := by
  cases t with
  | mk left current right =>
      cases right with
      | nil =>
          refine ⟨rfl, fun _ => rfl, ?_⟩
          intro i
          cases i <;> simp [moveLeft, moveRight]
      | cons cell rest => exact Equivalent.refl _

end Tape

namespace Configuration

/-- Identical control and identical tape cells relative to the two heads.
Represented tape lengths may differ because of redundant outer blanks. -/
def Equivalent (c d : Configuration) : Prop :=
  c.pc = d.pc ∧ c.halted = d.halted ∧
    c.inputTape.Equivalent d.inputTape ∧ c.outputTape.Equivalent d.outputTape

theorem Equivalent.refl (c : Configuration) : c.Equivalent c :=
  ⟨rfl, rfl, Tape.Equivalent.refl _, Tape.Equivalent.refl _⟩

theorem Equivalent.symm {c d : Configuration} (h : c.Equivalent d) :
    d.Equivalent c :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem Equivalent.outputBits {c d : Configuration} (h : c.Equivalent d) :
    c.outputBits = d.outputBits := h.2.2.2.bits

theorem Equivalent.tape {c d : Configuration} (h : c.Equivalent d) (tape : TapeId) :
    (c.tape tape).Equivalent (d.tape tape) := by
  cases tape
  · exact h.2.2.1
  · exact h.2.2.2

theorem Equivalent.updateTape {c d : Configuration} (h : c.Equivalent d)
    (tape : TapeId) (f : Tape → Tape)
    (hf : ∀ t s, t.Equivalent s → (f t).Equivalent (f s)) :
    (c.updateTape tape f).Equivalent (d.updateTape tape f) := by
  cases tape
  · exact ⟨h.1, h.2.1, hf _ _ h.2.2.1, h.2.2.2⟩
  · exact ⟨h.1, h.2.1, h.2.2.1, hf _ _ h.2.2.2⟩

theorem Equivalent.advance {c d : Configuration} (h : c.Equivalent d) :
    c.advance.Equivalent d.advance :=
  ⟨congrArg (· + 1) h.1, h.2⟩

theorem Equivalent.withPc {c d : Configuration} (h : c.Equivalent d) (pc : Nat) :
    ({ c with pc := pc } : Configuration).Equivalent { d with pc := pc } :=
  ⟨rfl, h.2⟩

theorem Equivalent.withHalted {c d : Configuration} (h : c.Equivalent d)
    (halted : Bool) :
    ({ c with halted := halted } : Configuration).Equivalent
      { d with halted := halted } :=
  ⟨h.1, rfl, h.2.2⟩

end Configuration

/-- The same actual transition is available from an equivalent physical
representation. Extra outer blanks do not charge a normalization step and
cannot change which random-bit choice this transition represents. -/
theorem Step.exists_equivalent {p : Program} {start finish other : Configuration}
    (step : Step p start finish) (h : start.Equivalent other) :
    ∃ target, Step p other target ∧ finish.Equivalent target := by
  have hc : start.halted = false := by
    cases hh : start.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  have hd : other.halted = false := h.2.1.symm.trans hc
  cases hInstr : p[start.pc]? with
  | none =>
      have hOther : p[other.pc]? = none := by simpa [← h.1] using hInstr
      simp [Step, successors, next, hc, hInstr] at step
      subst finish
      exact ⟨{ other with halted := true }, by simp [Step, successors, next, hd, hOther],
        h.withHalted true⟩
  | some instr =>
      have hOther : p[other.pc]? = some instr := by simpa [← h.1] using hInstr
      cases instr with
      | halt =>
          simp [Step, successors, next, hc, hInstr, Instruction.next] at step
          subst finish
          exact ⟨{ other with halted := true },
            by simp [Step, successors, next, hd, hOther, Instruction.next], h.withHalted true⟩
      | jump pc =>
          simp [Step, successors, next, hc, hInstr, Instruction.next] at step
          subst finish
          exact ⟨{ other with pc := pc },
            by simp [Step, successors, next, hd, hOther, Instruction.next], by simpa only [hc] using h.withPc pc⟩
      | moveLeft tape =>
          simp [Step, successors, next, hc, hInstr, Instruction.next] at step
          subst finish
          exact ⟨_, by simp [Step, successors, next, hd, hOther, Instruction.next],
            (h.updateTape tape Tape.moveLeft (fun _ _ ht => ht.moveLeft)).advance⟩
      | moveRight tape =>
          simp [Step, successors, next, hc, hInstr, Instruction.next] at step
          subst finish
          exact ⟨_, by simp [Step, successors, next, hd, hOther, Instruction.next],
            (h.updateTape tape Tape.moveRight (fun _ _ ht => ht.moveRight)).advance⟩
      | write tape bit =>
          simp [Step, successors, next, hc, hInstr, Instruction.next] at step
          subst finish
          exact ⟨_, by simp [Step, successors, next, hd, hOther, Instruction.next],
            (h.updateTape tape (fun t => t.write (some bit)) (fun _ _ ht => ht.write _)).advance⟩
      | erase tape =>
          simp [Step, successors, next, hc, hInstr, Instruction.next] at step
          subst finish
          exact ⟨_, by simp [Step, successors, next, hd, hOther, Instruction.next],
            (h.updateTape tape (fun t => t.write none) (fun _ _ ht => ht.write _)).advance⟩
      | branch tape blankPc zeroPc onePc =>
          have hCell := (h.tape tape).1
          cases hCurrent : (start.tape tape).current with
          | none =>
              simp [Step, successors, next, hc, hInstr, Instruction.next, hCurrent] at step
              subst finish
              exact ⟨{ other with pc := blankPc },
                by simp [Step, successors, next, hd, hOther, Instruction.next, ← hCell, hCurrent],
                by simpa only [hc] using h.withPc blankPc⟩
          | some bit =>
              cases bit <;>
                simp [Step, successors, next, hc, hInstr, Instruction.next, hCurrent] at step <;>
                subst finish
              · exact ⟨{ other with pc := zeroPc },
                  by simp [Step, successors, next, hd, hOther, Instruction.next, ← hCell, hCurrent],
                  by simpa only [hc] using h.withPc zeroPc⟩
              · exact ⟨{ other with pc := onePc },
                  by simp [Step, successors, next, hd, hOther, Instruction.next, ← hCell, hCurrent],
                  by simpa only [hc] using h.withPc onePc⟩
      | randomBit tape =>
          simp [Step, successors, next, hc, hInstr, Instruction.next] at step
          rcases step with rfl | rfl
          · exact ⟨_, by simp [Step, successors, next, hd, hOther, Instruction.next],
              (h.updateTape tape (fun t => t.write (some false)) (fun _ _ ht => ht.write _)).advance⟩
          · exact ⟨_, by simp [Step, successors, next, hd, hOther, Instruction.next],
              (h.updateTape tape (fun t => t.write (some true)) (fun _ _ ht => ht.write _)).advance⟩

/-- An actual trace transfers to an equivalent starting representation
without adding or removing transitions, including on randomized branches. -/
theorem RunsFor.exists_equivalent {p : Program} {start finish other : Configuration} {used : Nat}
    (run : RunsFor p start finish used) (h : start.Equivalent other) :
    ∃ target, RunsFor p other target used ∧ finish.Equivalent target := by
  induction run with
  | zero => exact ⟨other, RunsFor.zero _, h⟩
  | succ prior last ih =>
      obtain ⟨middle, hPrior, hMiddle⟩ := ih
      obtain ⟨target, hLast, hTarget⟩ := last.exists_equivalent hMiddle
      exact ⟨target, RunsFor.succ hPrior hLast, hTarget⟩

/-- Inspection traces transfer across redundant blank representations at
the same budget. Post-halt stutters remain inspection only. -/
theorem PaddedRunsFor.exists_equivalent {p : Program}
    {start finish other : Configuration} {steps : Nat}
    (run : PaddedRunsFor p start finish steps) (h : start.Equivalent other) :
    ∃ target, PaddedRunsFor p other target steps ∧ finish.Equivalent target := by
  induction run with
  | zero => exact ⟨other, PaddedRunsFor.zero _, h⟩
  | succ prior last ih =>
      obtain ⟨middle, hPrior, hMiddle⟩ := ih
      rcases last with last | ⟨hHalt, rfl⟩
      · obtain ⟨target, hLast, hTarget⟩ := last.exists_equivalent hMiddle
        exact ⟨target, PaddedRunsFor.succ hPrior (Or.inl hLast), hTarget⟩
      · exact ⟨middle, PaddedRunsFor.succ hPrior
          (Or.inr ⟨hMiddle.2.1.symm.trans hHalt, rfl⟩), hMiddle⟩

/-- One machine step respects tape-cell equivalence, including its exact
fair-bit probabilities. `k` is any observation of the next configuration
that depends only on control and tape cells, not redundant outer blanks. -/
theorem stepPMF_bind_eq_of_equivalent {α : Type*} (p : Program)
    (c d : Configuration) (h : c.Equivalent d) (k : Configuration → PMF α)
    (hk : ∀ c d, c.Equivalent d → k c = k d) :
    (stepPMF p c).bind k = (stepPMF p d).bind k := by
  by_cases hHalt : c.halted = true
  · have hd : d.halted = true := h.2.1.symm.trans hHalt
    simpa [stepPMF, next, hHalt, hd] using hk c d h
  · have hc : c.halted = false := by cases hh : c.halted <;> simp_all
    have hd : d.halted = false := h.2.1.symm.trans hc
    cases hInstr : p[c.pc]? with
    | none =>
        have hOther : p[d.pc]? = none := by simpa [← h.1] using hInstr
        simpa [stepPMF, next, hc, hd, hInstr, hOther] using
          hk _ _ (h.withHalted true)
    | some instr =>
        have hOther : p[d.pc]? = some instr := by simpa [← h.1] using hInstr
        have hUpdate (tape : TapeId) (f : Tape → Tape)
            (hf : ∀ t s, t.Equivalent s → (f t).Equivalent (f s)) :
            k ((c.updateTape tape f).advance) =
              k ((d.updateTape tape f).advance) :=
          hk _ _ ((h.updateTape tape f hf).advance)
        cases instr with
        | halt =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hk _ _ (h.withHalted true)
        | jump pc =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hk _ _ (h.withPc pc)
        | moveLeft tape =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hUpdate tape Tape.moveLeft (fun _ _ ht => ht.moveLeft)
        | moveRight tape =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hUpdate tape Tape.moveRight (fun _ _ ht => ht.moveRight)
        | write tape bit =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hUpdate tape (fun t => t.write (some bit)) (fun _ _ ht => ht.write _)
        | erase tape =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hUpdate tape (fun t => t.write none) (fun _ _ ht => ht.write _)
        | branch tape blankPc zeroPc onePc =>
            have hCell := (h.tape tape).1
            cases hCurrent : (c.tape tape).current with
            | none =>
                simpa [stepPMF, next, hc, hd, hInstr, hOther,
                  Instruction.next, ← hCell, hCurrent] using hk _ _ (h.withPc blankPc)
            | some bit =>
                cases bit <;>
                  simpa [stepPMF, next, hc, hd, hInstr, hOther,
                    Instruction.next, ← hCell, hCurrent] using hk _ _ (h.withPc _)
        | randomBit tape =>
            simp only [stepPMF, next, hc, hd, Bool.false_eq_true, ↓reduceIte,
              hInstr, hOther, Instruction.next, PMF.bind_map, Function.comp_def]
            congr 1
            funext bit
            cases bit <;> exact hUpdate tape _ (fun _ _ ht => ht.write _)

/-- Redundant outer blanks do not affect any distribution of observations,
at any fixed number of machine transitions. No normalization is performed
as part of execution; both representations execute the original program. -/
theorem evalConfigWithin_map_eq_of_equivalent {α : Type*} (p : Program)
    (c d : Configuration) (h : c.Equivalent d) (steps : Nat)
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin p c steps).map observe =
      (evalConfigWithin p d steps).map observe := by
  induction steps generalizing c d with
  | zero => simp [evalConfigWithin, PMF.pure_map, hObserve c d h]
  | succ steps ih =>
      rw [evalConfigWithin_succ_head, evalConfigWithin_succ_head,
        PMF.map_bind, PMF.map_bind]
      exact stepPMF_bind_eq_of_equivalent p c d h _ (fun c d h => ih c d h)

/-- Timeout and successful output distributions are unchanged by redundant
outer blanks. This assertion holds even when execution has not yet halted. -/
theorem Configuration.Equivalent.evalOutput {c d : Configuration}
    (h : c.Equivalent d) (p : Program) (steps : Nat) :
    (evalConfigWithin p c steps).map
        (fun e => if e.halted then some e.outputBits else none) =
      (evalConfigWithin p d steps).map
        (fun e => if e.halted then some e.outputBits else none) := by
  apply evalConfigWithin_map_eq_of_equivalent p c d h steps
  intro c d h
  rw [h.2.1, h.outputBits]

/-- The same transition-count bound holds on every random branch from an
equivalent initial tape representation. The support theorem connects this
universal claim to actual padded operational traces, not a selected branch. -/
theorem HaltsWithin.of_equivalent_initial
    {p : Program} {input : List Bool} {bound : Nat} {start : Configuration}
    (halts : HaltsWithin p input bound)
    (h : (Configuration.initial input).Equivalent start) :
    ∀ finish, PaddedRunsFor p start finish bound → finish.halted = true := by
  intro finish run
  have hEval := evalConfigWithin_map_eq_of_equivalent p
    (Configuration.initial input) start h bound Configuration.halted
    (fun _ _ he => he.2.1)
  have hSupport : finish.halted ∈
      ((evalConfigWithin p start bound).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff p start finish bound).mpr run, rfl⟩
  rw [← hEval] at hSupport
  rw [PMF.mem_support_map_iff] at hSupport
  obtain ⟨sourceFinish, hSourceSupport, hFlag⟩ := hSupport
  exact hFlag.symm.trans (halts sourceFinish
    ((mem_support_evalConfigWithin_iff p _ sourceFinish bound).mp hSourceSupport))

/-- A caller need only prepare tapes equivalent to the source's initial
tapes. Redundant outer blank cells need not be removed from the mathematical
zipper representation. This theorem charges no free cleanup operation. -/
theorem HaltsWithin.withSubroutine_returnsWithin_of_equivalent
    (pre source suffix : Program) (returnPc : Nat)
    {input : List Bool} {bound : Nat} {start : Configuration}
    (halts : HaltsWithin source input bound)
    (h : (Configuration.initial input).Equivalent start) :
    ReturnsWithin (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) returnPc bound := by
  intro finish run
  by_contra hNoReturn
  have hpc : start.pc ≤ source.length := by
    have := h.1
    simp only [Configuration.initial] at this
    omega
  have hActive : start.halted = false := by
    simpa only [Configuration.initial] using h.2.1.symm
  obtain ⟨sourceFinish, hSourceRun, hSourceActive, _, _⟩ :=
    run.source_of_not_returned pre source suffix returnPc hpc hActive hNoReturn
  have hHalted := halts.of_equivalent_initial h sourceFinish hSourceRun.toPadded
  simp [hSourceActive] at hHalted

/-- Probability semantics of a call likewise requires cell equivalence,
not literal equality of finite zipper records. Layout and tape preparation
remain explicit obligations of the caller. -/
theorem HaltsWithin.withSubroutine_evalReturn_of_equivalent
    (pre source suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ source.length → pre.length + pc ≠ returnPc)
    {input : List Bool} {bound : Nat} {start : Configuration}
    (halts : HaltsWithin source input bound)
    (h : (Configuration.initial input).Equivalent start) :
    (evalReturnWithin (Program.withSubroutine pre source suffix returnPc)
      returnPc (start.rebasePc pre.length) bound).map
        (fun e => if e.pc = returnPc then some e.outputBits else none) =
      evalWithin source input bound := by
  have hpc : start.pc ≤ source.length := by
    have := h.1
    simp only [Configuration.initial] at this
    omega
  have hActive : start.halted = false := by
    simpa only [Configuration.initial] using h.2.1.symm
  let invocation := evalReturnWithin
    (Program.withSubroutine pre source suffix returnPc) returnPc
    (start.rebasePc pre.length) bound
  have hReturned : ∀ finish ∈ invocation.support, finish.pc = returnPc := by
    intro finish hFinish
    exact halts.withSubroutine_returnsWithin_of_equivalent pre source suffix
      returnPc h finish ((mem_support_evalReturnWithin_iff pre source suffix
        returnPc hpc hActive finish bound).mp hFinish)
  have hInvocation : invocation.map
      (fun e => if e.pc = returnPc then some e.outputBits else none) =
        invocation.map (fun e => some e.outputBits) := by
    change (invocation.bind fun e => PMF.pure
      (if e.pc = returnPc then some e.outputBits else none)) =
        (invocation.bind fun e => PMF.pure (some e.outputBits))
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext finish hFinish
    simp [hReturned finish hFinish]
  have hSource : evalWithin source input bound =
      (evalConfigWithin source (Configuration.initial input) bound).map
        (fun e => some e.outputBits) := by
    change ((evalConfigWithin source (Configuration.initial input) bound).bind
      fun e => PMF.pure (if e.halted then some e.outputBits else none)) = _
    change _ = ((evalConfigWithin source (Configuration.initial input) bound).bind
      fun e => PMF.pure (some e.outputBits))
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext finish hFinish
    have hHalted := halts finish
      ((mem_support_evalConfigWithin_iff source _ finish bound).mp hFinish)
    simp [hHalted]
  rw [hInvocation, hSource]
  have hInvocationOutput := Program.evalReturnWithin_output_eq pre source suffix
    returnPc hLayout start hpc hActive bound
  have hSourceOutput := evalConfigWithin_map_eq_of_equivalent source
    (Configuration.initial input) start h bound Configuration.outputBits
      (fun _ _ he => he.outputBits)
  have hOutput := hInvocationOutput.trans hSourceOutput.symm
  simpa only [PMF.map_comp, Function.comp_def] using
    congrArg (fun p : PMF (List Bool) => p.map some) hOutput

end Machine
