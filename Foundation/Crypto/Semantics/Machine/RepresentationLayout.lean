import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! Separate cell contents from the finite zipper representation. Lengths
on both sides of each head recover the exact represented padding from any
cell-equivalent configuration. Reconstruction is a mathematical function,
not a free normalization or allocation instruction. -/
namespace Machine.Tape

structure Layout where
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def layout (tape : Tape) : Layout := ⟨tape.left.length, tape.right.length⟩

def reconstruct (shape : Layout) (cells : Tape) : Tape where
  left := List.ofFn (fun i : Fin shape.left => cells.left.getD i.val none)
  current := cells.current
  right := List.ofFn (fun i : Fin shape.right => cells.right.getD i.val none)

private theorem ofFn_getD (cells : List (Option Bool)) :
    List.ofFn (fun i : Fin cells.length => cells.getD i.val none) = cells := by
  calc
    _ = List.ofFn (fun i : Fin cells.length => cells[i.val]) := by
      congr 1
      funext i
      exact (List.getElem_eq_getD none).symm
    _ = cells := List.ofFn_getElem

theorem reconstruct_eq_of_equivalent (actual cells : Tape) (equivalent : actual.Equivalent cells) :
    reconstruct actual.layout cells = actual := by
  have hLeft : List.ofFn (fun i : Fin actual.left.length => cells.left.getD i.val none) = actual.left := by
    calc
      _ = List.ofFn (fun i : Fin actual.left.length => actual.left.getD i.val none) := by
        congr 1
        funext i
        exact (equivalent.2.1 i.val).symm
      _ = actual.left := ofFn_getD _
  have hRight : List.ofFn (fun i : Fin actual.right.length => cells.right.getD i.val none) = actual.right := by
    calc
      _ = List.ofFn (fun i : Fin actual.right.length => actual.right.getD i.val none) := by
        congr 1
        funext i
        exact (equivalent.2.2 i.val).symm
      _ = actual.right := ofFn_getD _
  cases actual
  cases cells
  simp only [reconstruct, layout, Tape.mk.injEq]
  exact ⟨hLeft, equivalent.1.symm, hRight⟩

theorem eq_of_equivalent_of_layout_eq (first second : Tape) (equivalent : first.Equivalent second)
    (sameLayout : first.layout = second.layout) : first = second := by
  have h := reconstruct_eq_of_equivalent first second equivalent
  rw [sameLayout, reconstruct_eq_of_equivalent second second (Equivalent.refl second)] at h
  exact h.symm

end Machine.Tape

namespace Machine.Configuration

structure Layout where
  input : Tape.Layout
  output : Tape.Layout
  deriving DecidableEq, Repr

def layout (state : Configuration) : Layout := ⟨state.inputTape.layout, state.outputTape.layout⟩

def reconstruct (shape : Layout) (cells : Configuration) : Configuration :=
  { pc := cells.pc
    inputTape := Tape.reconstruct shape.input cells.inputTape
    outputTape := Tape.reconstruct shape.output cells.outputTape
    halted := cells.halted }

theorem reconstruct_eq_of_equivalent (actual cells : Configuration) (equivalent : actual.Equivalent cells) :
    reconstruct actual.layout cells = actual := by
  have hInput := Tape.reconstruct_eq_of_equivalent actual.inputTape cells.inputTape equivalent.2.2.1
  have hOutput := Tape.reconstruct_eq_of_equivalent actual.outputTape cells.outputTape equivalent.2.2.2
  cases actual
  cases cells
  simp only [reconstruct, layout, Configuration.mk.injEq]
  exact ⟨equivalent.1.symm, hInput, hOutput, equivalent.2.1.symm⟩

theorem eq_of_equivalent_of_layout_eq (first second : Configuration) (equivalent : first.Equivalent second)
    (sameLayout : first.layout = second.layout) : first = second := by
  have h := reconstruct_eq_of_equivalent first second equivalent
  rw [sameLayout, reconstruct_eq_of_equivalent second second (Equivalent.refl second)] at h
  exact h.symm

end Machine.Configuration
