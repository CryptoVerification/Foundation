import Foundation.Crypto.Logic.Polygraph.OracleRefreshCells

/-! Reconstruct an elementary diagram from a list of adjacent-swap positions.
The input contains no PMFs, semantic equalities, or enumerated proof paths.
The result is a typed Cell, hence its selected-kernel and joint-law theorems
follow from the primitive rules. This checks a supplied diagram; it does not
search all diagrams or prove a complexity separation from ordinary methods.
-/
namespace CryptoOracle.ProofEdits.Refresh.Certificate
variable {Index : Type}

def swapAt : Nat → (word : List Index) → Option (Σ target, Cell word target)
  | 0, first :: second :: tail => some ⟨second :: first :: tail, .exchange first second tail⟩
  | position + 1, first :: tail => (swapAt position tail).map fun result =>
      ⟨first :: result.1, .cons first result.2⟩
  | _, _ => none

def replay (word : List Index) : List Nat → Option (Σ target, Cell word target)
  | [] => some ⟨word, .refl word⟩
  | position :: rest => do
      let first ← swapAt position word
      let last ← replay first.1 rest
      pure ⟨last.1, .trans first.2 last.2⟩

def certify [DecidableEq Index] (word target : List Index) (positions : List Nat) : Option (Cell word target) :=
  match replay word positions with
  | none => none
  | some result => if same : result.1 = target then some (same ▸ result.2) else none

def accepts [DecidableEq Index] (word target : List Index) (positions : List Nat) : Bool :=
  (certify word target positions).isSome

theorem accepts_sound [DecidableEq Index] (word target : List Index) (positions : List Nat)
    (accepted : accepts word target positions = true) : Nonempty (Cell word target) := by
  unfold accepts at accepted
  cases checked : certify word target positions with
  | none => simp [checked] at accepted
  | some cell => exact ⟨cell⟩

theorem rejects_nonpermutation [DecidableEq Index] (word target : List Index)
    (different : ¬word.Perm target) (positions : List Nat) : accepts word target positions = false := by
  cases accepted : accepts word target positions with
  | false => rfl
  | true =>
      obtain ⟨cell⟩ := accepts_sound word target positions accepted
      exact False.elim (different cell.perm)

def nodes : {first second : List Index} → Cell first second → Nat
  | _, _, .refl _ => 1
  | _, _, .exchange _ _ _ => 1
  | _, _, .cons _ cell => 1 + nodes cell
  | _, _, .symm cell => 1 + nodes cell
  | _, _, .trans first second => 1 + nodes first + nodes second

theorem swapAt_nodes (position : Nat) (word target : List Index) (cell : Cell word target)
    (checked : swapAt position word = some ⟨target, cell⟩) : nodes cell ≤ position + 1 := by
  induction position generalizing word target with
  | zero =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first tail =>
          cases tail with
          | nil => simp [swapAt] at checked
          | cons second tail =>
              cases checked
              simp [nodes]
  | succ position ih =>
      cases word with
      | nil => simp [swapAt] at checked
      | cons first tail =>
          cases previous : swapAt position tail with
          | none => simp [swapAt, previous] at checked
          | some result =>
              rcases result with ⟨middle, step⟩
              simp only [swapAt, previous, Option.map_some, Option.some.injEq] at checked
              cases checked
              have bound := ih tail middle step previous
              simp only [nodes]
              omega

/-- Size is the number of elementary/context/composition nodes in the
constructed diagram, not source bytes or Lean kernel checking time. -/
theorem replay_nodes (positions : List Nat) (word target : List Index) (cell : Cell word target)
    (checked : replay word positions = some ⟨target, cell⟩) :
    nodes cell ≤ 1 + (positions.map (fun position => position + 2)).sum := by
  induction positions generalizing word target with
  | nil =>
      cases checked
      simp [nodes]
  | cons position rest ih =>
      cases first : swapAt position word with
      | none => simp [replay, first] at checked
      | some result =>
          rcases result with ⟨middle, firstCell⟩
          cases last : replay middle rest with
          | none => simp [replay, first, last] at checked
          | some result =>
              rcases result with ⟨final, lastCell⟩
              rw [replay, first] at checked
              change (replay middle rest).bind (fun result =>
                some (⟨result.1, Cell.trans firstCell result.2⟩ : Σ endpoint, Cell word endpoint)) =
                  some (⟨target, cell⟩ : Σ endpoint, Cell word endpoint) at checked
              rw [last] at checked
              cases checked
              have firstBound := swapAt_nodes position word middle firstCell first
              have lastBound := ih middle final lastCell last
              simp only [nodes, List.map_cons, List.sum_cons]
              omega

end CryptoOracle.ProofEdits.Refresh.Certificate
