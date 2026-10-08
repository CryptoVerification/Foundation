import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! Retain arbitrary finite blank padding while comparing the represented
cells. These are layout proofs; they execute no allocation or normalization. -/
namespace Machine.Tape

theorem getD_blank (cells : List (Option Bool)) (blank : ∀ cell ∈ cells, cell = none) (index : Nat) :
    cells.getD index none = none := by
  induction cells generalizing index with
  | nil => simp
  | cons cell rest ih =>
      have hCell := blank cell (by simp)
      have hRest : ∀ c ∈ rest, c = none := fun c h => blank c (by simp [h])
      cases index with
      | zero => exact hCell
      | succ index => simpa only [List.getD_cons_succ] using ih hRest index

theorem getD_append_blank (front padding : List (Option Bool))
    (blank : ∀ cell ∈ padding, cell = none) (index : Nat) :
    (front ++ padding).getD index none = front.getD index none := by
  induction front generalizing index with
  | nil => simpa using getD_blank padding blank index
  | cons cell rest ih =>
      cases index with
      | zero => rfl
      | succ index => simpa only [List.cons_append, List.getD_cons_succ] using ih index

theorem append_right_blank_equivalent (tape : Tape) (padding : List (Option Bool))
    (blank : ∀ cell ∈ padding, cell = none) :
    ({tape with right := tape.right ++ padding} : Tape).Equivalent tape :=
  ⟨rfl, fun _ => rfl, getD_append_blank tape.right padding blank⟩

theorem append_left_blank_equivalent (tape : Tape) (padding : List (Option Bool))
    (blank : ∀ cell ∈ padding, cell = none) :
    ({tape with left := tape.left ++ padding} : Tape).Equivalent tape :=
  ⟨rfl, getD_append_blank tape.left padding blank, fun _ => rfl⟩

end Machine.Tape
