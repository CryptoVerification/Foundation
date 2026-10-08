import Foundation.Crypto.Meta.General.Normalization
import Foundation.Crypto.Logic.General.Backends
import Foundation.Crypto.Semantics.Security.ThreeGames

/-! Arbitrarily long fixed finite hybrids built from the existing binary rule.
Each adjacent edge receives a certified copy of the same native attack code.
A zero-edge hybrid is separately reflexive and introduces no empty proof. -/
namespace CryptoLogic.General.FiniteHybrid

open Backends Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev Object := Nat × Nat

inductive Binary : Object → Object → Object → Type where
  | split (i j k : Nat) : Binary (i, k) (i, j) (j, k)

abbrev language : Language system where
  Object := Object
  machine := fun _ => Kind.native
  Unary := fun _ _ => PEmpty
  unaryCompiler := fun p => nomatch p
  Binary := Binary
  binaryCompilers := fun _ =>
    (.primitive (.native .identity), .primitive (.native .identity))

noncomputable def signature (games : Nat → CryptoLogic.ThreeGames.Game) : Signature language where
  interpret := fun (i, j) => nativeObject (CryptoLogic.ThreeGames.object (games i) (games j))
  unary := fun p => nomatch p
  unary_compiler := fun p => nomatch p
  binary := fun e => match e with
    | .split i j k => Native.binary (CryptoLogic.ThreeGames.reduction (games i) (games j) (games k))
  left_compiler := by intro X Y Z e; cases e; rfl
  right_compiler := by intro X Y Z e; cases e; rfl

@[macro_inline] def context (games : Nat → CryptoLogic.ThreeGames.Game) (count : Nat) :
    Context (signature games) where
  length := count
  claim i := ⟨(i.val, i.val + 1), fun _ => ()⟩

/-- Pure construction depends on the fixed number of edges, not on the games. -/
def plan (count : Nat) : ∀ (length : Nat), length + 1 ≤ count →
    Plan system (fun _ : Fin count => Kind.native) Kind.native
  | 0, h => Plan.hypothesis (K := system) (machines := fun _ : Fin count => Kind.native)
      ⟨0, by omega⟩ Kind.native rfl
  | length + 1, h =>
      .binary (.primitive (.native .identity)) (.primitive (.native .identity))
        (plan count length (by omega))
        (Plan.hypothesis (K := system) (machines := fun _ : Fin count => Kind.native)
          ⟨length + 1, by omega⟩ Kind.native rfl)

noncomputable def tree (games : Nat → CryptoLogic.ThreeGames.Game) (count : Nat) :
    ∀ (length : Nat), length + 1 ≤ count →
      Tree (signature games) (context games count) (0, length + 1) (fun _ => ())
  | 0, h => Tree.hypothesis (S := signature games) (Γ := context games count)
      ⟨0, by change 0 < count; omega⟩
  | length + 1, h =>
      Tree.binary (S := signature games) (Γ := context games count)
        (Binary.split 0 (length + 1) (length + 1 + 1)) (fun _ => ())
        (tree games count length (by omega))
        (Tree.hypothesis (S := signature games) (Γ := context games count)
          ⟨length + 1, by change length + 1 < count; omega⟩)

theorem tree_plan (games : Nat → CryptoLogic.ThreeGames.Game) (count length : Nat)
    (h : length + 1 ≤ count) : (tree games count length h).plan = plan count length h := by
  induction length with
  | zero => rfl
  | succ length ih =>
      change Plan.binary _ _ (tree games count length _).plan _ = Plan.binary _ _ (plan count length _) _
      rw [ih]
      rfl

@[macro_inline] def derivation (games : Nat → CryptoLogic.ThreeGames.Game) (length : Nat) :
    Derivation (signature games) (context games (length + 1)) (0, length + 1) (fun _ => ()) where
  plan := plan (length + 1) length (by omega)
  compilers := (plan (length + 1) length (by omega)).paths
  emitted_eq := Plan.paths_run _
  typed := ⟨tree games (length + 1) length (by omega), tree_plan _ _ _ _⟩

noncomputable def analysis (games : Nat → CryptoLogic.ThreeGames.Game) (length : Nat) :
    Derivation.Analysis (derivation games length) :=
  ⟨tree games (length + 1) length (by omega), tree_plan _ _ _ _⟩

/-- Every adjacent pair is used once in its original order. -/
theorem plan_run (count length : Nat) (h : length + 1 ≤ count) (code : Machine.Program) :
    ((plan count length h).run code).map (fun (i, packed) => (i.val, packed)) =
      (List.range (length + 1)).map (fun i => (i, (⟨Kind.native, code⟩ : Sigma system.Code))) := by
  induction length with
  | zero => rfl
  | succ length ih =>
      change (((plan count length _).run code) ++
        [((⟨length + 1, by omega⟩ : Fin count), (⟨Kind.native, code⟩ : Sigma system.Code))]).map
        (fun (i, packed) => (i.val, packed)) = _
      rw [List.map_append, ih]
      conv_rhs => rw [List.range_succ, List.map_append]
      rfl

theorem run (games : Nat → CryptoLogic.ThreeGames.Game) (length : Nat) (code : Machine.Program) :
    (derivation games length).run code =
      (List.range (length + 1)).map (fun i => (i, (⟨Kind.native, code⟩ : Sigma system.Code))) := by
  rw [Derivation.run_eq]
  exact plan_run _ _ _ code

/-- The explicit tree's loss is the sum over precisely the adjacent edges. -/
theorem tree_loss_eval (games : Nat → CryptoLogic.ThreeGames.Game) (count length : Nat)
    (h : length + 1 ≤ count) (ε : Fin count → Nat → ℝ≥0∞) (n : Nat) :
    (tree games count length h).loss.eval ε n =
      ∑ i : Fin (length + 1), ε ⟨i.val, by omega⟩ n := by
  induction length with
  | zero => simp [tree, Tree.loss, CryptoLogic.LossTree.eval]
  | succ length ih =>
      change (tree games count length _).loss.eval ε n + ε ⟨length + 1, _⟩ n = _
      rw [ih]
      symm
      rw [Fin.sum_univ_castSucc]
      rfl

theorem bounded (games : Nat → CryptoLogic.ThreeGames.Game) (length : Nat)
    (ε : Fin (length + 1) → Nat → ℝ≥0∞)
    (hε : ∀ i, (nativeObject (CryptoLogic.ThreeGames.object (games i.val) (games (i.val + 1)))).Bounded
      (fun _ => ()) (ε i)) :
    (nativeObject (CryptoLogic.ThreeGames.object (games 0) (games (length + 1)))).Bounded
      (fun _ => ()) (fun n => ∑ i, ε i n) := by
  intro A hA n
  have hb := (analysis games length).bounded ε hε A hA n
  dsimp [analysis, Derivation.Analysis.loss] at hb
  change advantageProfile _ _ _ n ≤ (tree games (length + 1) length _).loss.eval ε n at hb
  rw [tree_loss_eval] at hb
  exact hb

theorem secure (games : Nat → CryptoLogic.ThreeGames.Game) (length : Nat)
    (h : ∀ i : Fin (length + 1),
      (nativeObject (CryptoLogic.ThreeGames.object (games i.val) (games (i.val + 1)))).Secure (fun _ => ())) :
    (nativeObject (CryptoLogic.ThreeGames.object (games 0) (games (length + 1)))).Secure (fun _ => ()) := by
  apply (derivation games length).sound
  exact h

/-- The degenerate zero-edge case is semantic reflexivity, not an empty
context derivation of an arbitrary security claim. -/
theorem bounded_zero (game : CryptoLogic.ThreeGames.Game) :
    (nativeObject (CryptoLogic.ThreeGames.object game game)).Bounded
      (fun _ => ()) (fun _ => 0) := by
  intro A hA n
  simp [advantageProfile, nativeObject, CryptoLogic.ThreeGames.object,
    CryptoLogic.ThreeGames.goal, CryptoLogic.SecurityObject.ppt, probabilityGap]

theorem bounded_uniform (games : Nat → CryptoLogic.ThreeGames.Game) (length : Nat)
    (ε : Nat → ℝ≥0∞)
    (hε : ∀ i : Fin (length + 1),
      (nativeObject (CryptoLogic.ThreeGames.object (games i.val) (games (i.val + 1)))).Bounded
        (fun _ => ()) ε) :
    (nativeObject (CryptoLogic.ThreeGames.object (games 0) (games (length + 1)))).Bounded
      (fun _ => ()) (fun n => (length + 1 : Nat) * ε n) := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    bounded games length (fun _ => ε) hε

/-- Every emitted adjacent-edge program inherits the same genuine native
stopping budget as the original witness. This covers all code occurrences. -/
theorem emitted_halts (games : Nat → CryptoLogic.ThreeGames.Game) (length : Nat)
    (A) (W : (nativeObject (CryptoLogic.ThreeGames.object (games 0)
      (games (length + 1)))).Witness (fun _ => ()) A)
    (entry : Nat × Sigma system.Code)
    (he : entry ∈ (derivation games length).run W.code) (input : List Bool) :
    ∃ i, i < length + 1 ∧ entry = (i, ⟨Kind.native, W.code⟩) ∧
      Machine.HaltsWithin W.code input (W.resources input.length) := by
  rw [run, List.mem_map] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨i, List.mem_range.mp hi, rfl, W.executes.2 input⟩

/-- The sum accounts for running each adjacent-edge program separately.
It is not the runtime of a newly concatenated adversary. -/
theorem total_budget (games : Nat → CryptoLogic.ThreeGames.Game) (length : Nat)
    (code : Machine.Program) (budget : Nat → Nat) (size : Nat) :
    (((derivation games length).run code).map (fun _ => budget size)).sum =
      (length + 1) * budget size := by
  rw [run, List.map_map]
  change ((List.range (length + 1)).map (fun _ : Nat => budget size)).sum = _
  simp


end CryptoLogic.General.FiniteHybrid
