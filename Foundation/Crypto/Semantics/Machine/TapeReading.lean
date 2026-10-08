import Foundation.Crypto.Semantics.Machine.Basic

/-! Head motion preserves the finite bit observation, including motion into
blank space. This is an equality of observations, not equality of physical
tapes or an instruction that reads an entire tape in constant time. -/
namespace Machine.Tape

@[simp] theorem bits_moveRight (tape : Tape) : tape.moveRight.bits = tape.bits := by
  rcases tape with ⟨left, current, right⟩
  cases right <;> simp [moveRight, bits, List.reverse_cons, List.append_assoc]
  all_goals simp only [← List.filterMap_append, List.singleton_append]

@[simp] theorem bits_moveLeft (tape : Tape) : tape.moveLeft.bits = tape.bits := by
  rcases tape with ⟨left, current, right⟩
  cases left <;> simp [moveLeft, bits, List.reverse_cons, List.append_assoc]
  all_goals simp only [← List.filterMap_append, List.singleton_append]

@[simp] theorem bits_ofBits (bits : List Bool) : (ofBits bits).bits = bits := by
  cases bits <;> simp [ofBits, Tape.bits]

end Machine.Tape
