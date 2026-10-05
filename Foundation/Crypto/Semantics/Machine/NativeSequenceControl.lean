import Foundation.Crypto.Semantics.Machine.NativeSequence

namespace Machine

private def targetsInside (limit pc : Nat) : Instruction → Prop
  | .halt => True
  | .jump target => target < limit
  | .branch _ a b c => a < limit ∧ b < limit ∧ c < limit
  | _ => pc + 1 < limit

private theorem step_inside (p : Program)
    (safe : ∀ pc : Fin p.length, targetsInside p.length pc.val p[pc.val])
    (c d : Configuration) (hc : c.pc < p.length) (step : Step p c d)
    (active : d.halted = false) : d.pc < p.length := by
  have h := safe ⟨c.pc, hc⟩
  change targetsInside p.length c.pc p[c.pc] at h
  have running : c.halted = false := by
    cases hh : c.halted
    · rfl
    · exact False.elim ((no_step_of_halted hh) step)
  simp only [Step, successors, next, running, Bool.false_eq_true, ↓reduceIte,
    List.getElem?_eq_getElem hc] at step
  cases hi : p[c.pc] with
  | halt => simp [hi, Instruction.next] at step; subst d; simp at active
  | jump target =>
    simp only [hi, Instruction.next, List.mem_singleton] at step
    subst d
    simpa only [hi, targetsInside] using h
  | branch tape a b e =>
    simp only [hi, Instruction.next, List.mem_singleton] at step
    subst d
    simp only [hi, targetsInside] at h
    cases ht : (c.tape tape).current with
    | none => exact h.1
    | some bit => cases bit; exact h.2.1; exact h.2.2
  | moveLeft tape | moveRight tape | write tape bit | erase tape =>
    cases tape <;> simp_all [Instruction.next, Configuration.advance,
      Configuration.updateTape, targetsInside]
  | randomBit tape =>
    cases tape <;> simp only [hi, Instruction.next, List.mem_cons, List.mem_nil_iff, or_false,
      Configuration.advance, Configuration.updateTape] at step
    all_goals rcases step with rfl | rfl <;> simpa only [hi, targetsInside] using h

private theorem relocated_inside (i : Instruction) (base ret size pc limit : Nat)
    (hReturn : ret < limit) (hBlock : base + size < limit) (hPc : pc < size) :
    targetsInside limit (base+pc) (i.asSubroutine base ret size) := by
  have address (a : Nat) : subroutineAddress base ret size a < limit := by
    unfold subroutineAddress
    split <;> omega
  cases i <;> simp only [Instruction.asSubroutine, targetsInside]
  all_goals first | exact hReturn | exact address _ | exact ⟨address _, address _, address _⟩ | omega

/-- Relocated sequential code cannot escape its finite instruction list.
This includes random branches and does not assert that they terminate. -/
theorem Program.followedBy_control_closed (first second : Program) :
    ∀ c d, c.pc < (first.followedBy second).length →
      Step (first.followedBy second) c d → d.halted = false →
      d.pc < (first.followedBy second).length := by
  apply step_inside
  rintro ⟨pc, pcBound⟩
  change targetsInside (first.followedBy second).length pc (first.followedBy second)[pc]
  have hpc := pcBound
  have length : (first.followedBy second).length = first.length+second.length+3 := by
    simp [Program.followedBy]; omega
  simp only [length] at hpc ⊢
  by_cases one : pc < first.length
  · have lookup : (first.followedBy second)[pc]? =
        some ((first[pc]).asSubroutine 0 (first.length+1) first.length) := by
      simp only [Program.followedBy, List.append_assoc]
      rw [List.getElem?_append_left (by simp; omega),
        Program.asSubroutine_getElem?_source _ _ _ _ one,
        List.getElem?_eq_getElem one]
      rfl
    rw [List.getElem?_eq_getElem pcBound] at lookup
    rw [Option.some.inj lookup]
    simpa using relocated_inside first[pc] 0 (first.length+1) first.length pc
      (first.length+second.length+3) (by omega) (by omega) one
  · by_cases boundary : pc = first.length
    · have lookup : (first.followedBy second)[pc]? = some (.jump (first.length+1)) := by
        simp only [Program.followedBy, List.append_assoc, boundary]
        rw [List.getElem?_append_left (by simp), Program.asSubroutine_getElem?_return]
      rw [List.getElem?_eq_getElem pcBound] at lookup
      rw [Option.some.inj lookup]
      simp only [targetsInside]; omega
    · have beyond : first.length+1 ≤ pc := by omega
      by_cases two : pc-(first.length+1) < second.length
      · have lookup : (first.followedBy second)[pc]? =
            some ((second[pc-(first.length+1)]).asSubroutine
              (first.length+1) (first.length+second.length+2) second.length) := by
          simp only [Program.followedBy, List.append_assoc]
          rw [List.getElem?_append_right (by simp; omega)]
          simp only [Program.asSubroutine_length]
          rw [List.getElem?_append_left (by simp; omega),
            Program.asSubroutine_getElem?_source _ _ _ _ two,
            List.getElem?_eq_getElem two]
          rfl
        rw [List.getElem?_eq_getElem pcBound] at lookup
        rw [Option.some.inj lookup]
        have position : first.length+1+(pc-(first.length+1)) = pc := by omega
        have safe := relocated_inside second[pc-(first.length+1)]
          (first.length+1) (first.length+second.length+2) second.length
          (pc-(first.length+1)) (first.length+second.length+3) (by omega) (by omega) two
        simpa only [position] using safe
      · have endPc : pc = first.length+second.length+2 ∨
            pc = first.length+second.length+1 := by omega
        rcases endPc with final | ret
        · have lookup : (first.followedBy second)[pc]? = some .halt := by
            simp only [Program.followedBy, List.append_assoc]
            rw [List.getElem?_append_right (by simp; omega)]
            simp only [Program.asSubroutine_length]
            rw [List.getElem?_append_right (by simp; omega)]
            have index : pc-(first.length+1)-(second.length+1) = 0 := by omega
            simp only [Program.asSubroutine_length]
            rw [index]; rfl
          rw [List.getElem?_eq_getElem pcBound] at lookup
          rw [Option.some.inj lookup]; trivial
        · have lookup : (first.followedBy second)[pc]? =
              some (.jump (first.length+second.length+2)) := by
            simp only [Program.followedBy, List.append_assoc]
            rw [List.getElem?_append_right (by simp; omega)]
            simp only [Program.asSubroutine_length]
            have index : pc-(first.length+1) = second.length := by omega
            rw [index, List.getElem?_append_left (by simp), Program.asSubroutine_getElem?_return]
          rw [List.getElem?_eq_getElem pcBound] at lookup
          rw [Option.some.inj lookup]; simp only [targetsInside]; omega

end Machine
