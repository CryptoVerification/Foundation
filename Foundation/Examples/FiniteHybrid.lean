import Foundation.Crypto.Meta.General.FiniteHybrid
import Foundation.Examples.GeneralResources

namespace CryptoLogic.General.FiniteHybridExamples

open Backends Foundation.Probability
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal

noncomputable def games (i : Nat) : CryptoLogic.ThreeGames.Game :=
  if i = 0 then fun _ A => A false else
    if i = 4 then fun _ A => A true else fun _ A => sampleBit.bind A

-- Noncomputable game distributions are not evaluated to emit the four codes.
/-- info: true -/
#guard_msgs in
#eval
  ((FiniteHybrid.derivation games 3).run [.randomBit .output, .halt]).map
    (fun (i, c) => (i, Examples.summary c)) ==
    [(0, Kind.native, false, 2), (1, Kind.native, false, 2),
     (2, Kind.native, false, 2), (3, Kind.native, false, 2)]

/-- info: true -/
#guard_msgs in
#eval ((FiniteHybrid.derivation games 3).normalize.run [.randomBit .output, .halt]).map
    (fun (i, c) => (i, Examples.summary c)) ==
    [(0, Kind.native, false, 2), (1, Kind.native, false, 2),
     (2, Kind.native, false, 2), (3, Kind.native, false, 2)]

example (g : Nat → CryptoLogic.ThreeGames.Game) (k : Nat) (p : Machine.Program) :
    (FiniteHybrid.derivation g k).run p =
      (List.range (k + 1)).map (fun i => (i, (⟨Kind.native, p⟩ : Sigma system.Code))) :=
  FiniteHybrid.run g k p

example (g : Nat → CryptoLogic.ThreeGames.Game) (k : Nat)
    (ε : Fin (k + 1) → Nat → ℝ≥0∞)
    (h : ∀ i, (nativeObject (CryptoLogic.ThreeGames.object (g i.val) (g (i.val + 1)))).Bounded
      (fun _ => ()) (ε i)) :
    (nativeObject (CryptoLogic.ThreeGames.object (g 0) (g (k + 1)))).Bounded
      (fun _ => ()) (fun n => ∑ i, ε i n) := FiniteHybrid.bounded g k ε h

example (g : Nat → CryptoLogic.ThreeGames.Game) (k : Nat) :
    (FiniteHybrid.derivation g k).extract.length = k + 1 := by
  have h := congrArg List.length ((FiniteHybrid.derivation g k).extract_emitted [.halt])
  rw [List.length_map, FiniteHybrid.run, List.length_map, List.length_range] at h
  exact h

example : (FiniteHybrid.analysis games 3).loss.eval (fun _ _ => (1 : ℝ≥0∞)) 0 = 4 := by
  change (FiniteHybrid.tree games 4 3 (by decide)).loss.eval _ _ = _
  rw [FiniteHybrid.tree_loss_eval]
  norm_num [Fin.sum_univ_succ]

end CryptoLogic.General.FiniteHybridExamples
