import Foundation.Crypto.Meta.General.FiniteHybrid
import Foundation.Crypto.Meta.Polygraph.Normalization
import Foundation.Crypto.Logic.Polygraph.ExperimentSyntax

/-! Pure finite hybrid diagrams. The syntax depends on the number of edges,
not on any games or security witnesses. Every occurrence is interpreted in
order, with its complete native execution certificate. -/
namespace CryptoLogic.Polygraph.FiniteHybrid

open General General.Backends
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

abbrev language := General.FiniteHybrid.language

abbrev parameters : Presented.Parameters language where
  Family := fun _ => Unit
  unary := fun _ _ => ()
  left := fun _ _ => ()
  right := fun _ _ => ()

abbrev context (count : Nat) : Presented.Context parameters where
  length := count
  claim i := ⟨(i.val, i.val + 1), ()⟩

def partialProof (count : Nat) : (length : Nat) → length + 1 ≤ count →
    Derivation parameters (context count) (0, length + 1) ()
  | 0, h => Derivation.hypothesis (P := parameters) (Γ := context count)
      ⟨0, by change 0 < count; omega⟩
  | length + 1, h =>
      Derivation.binary (P := parameters) (Γ := context count)
        (.split 0 (length + 1) (length + 1 + 1)) ()
        (partialProof count length (by omega))
        (Derivation.hypothesis (P := parameters) (Γ := context count)
          ⟨length + 1, by change length + 1 < count; omega⟩)

def proof (length : Nat) : Derivation parameters (context (length + 1)) (0, length + 1) () :=
  partialProof (length + 1) length (by omega)

noncomputable def interpretation (games : Nat → ThreeGames.Game) :
    Presented.Interpretation parameters (General.FiniteHybrid.signature games) where
  family := fun _ _ => ()
  unary := by
    intro X Y r F
    induction r with
    | identity => rfl
    | primitive p => nomatch p
    | seq r s ihr ihs => rfl
  left := by intros; rfl
  right := by intros; rfl

theorem tree_partialProof (games : Nat → ThreeGames.Game) (count length : Nat)
    (h : length + 1 ≤ count) :
    Derivation.tree (interpretation games) (partialProof count length h) =
      General.FiniteHybrid.tree games count length h := by
  induction length with
  | zero => rfl
  | succ length ih =>
      change General.Tree.binary (S := General.FiniteHybrid.signature games)
        (Γ := General.FiniteHybrid.context games count)
        (.split 0 (length + 1) (length + 1 + 1)) (fun _ => ())
        (Derivation.tree (interpretation games) (partialProof count length _)) _ = _
      rw [ih]
      rfl

theorem plan_partialProof (count length : Nat) (h : length + 1 ≤ count) :
    Derivation.plan (partialProof count length h) = General.FiniteHybrid.plan count length h := by
  induction length with
  | zero => rfl
  | succ length ih =>
      change Plan.binary _ _ (Derivation.plan (partialProof count length _)) _ = _
      rw [ih]
      rfl

theorem run (length : Nat) (code : Machine.Program) :
    Derivation.run (proof length) code = (List.range (length + 1)).map
      (fun i => (i, (⟨Kind.native, code⟩ : Sigma system.Code))) := by
  change ((Derivation.plan (partialProof _ _ _)).run code).map _ = _
  rw [plan_partialProof]
  exact General.FiniteHybrid.plan_run _ _ _ code

theorem loss (games : Nat → ThreeGames.Game) (length : Nat)
    (ε : Fin (length + 1) → Nat → ℝ≥0∞) (n : Nat) :
    (Derivation.loss (interpretation games) (proof length)).eval ε n = ∑ i, ε i n := by
  unfold Derivation.loss Presented.Interpretation.loss
  change (Derivation.tree (interpretation games) (partialProof _ _ _)).loss.eval ε n = _
  rw [tree_partialProof, General.FiniteHybrid.tree_loss_eval]

theorem bounded (games : Nat → ThreeGames.Game) (length : Nat)
    (ε : Fin (length + 1) → Nat → ℝ≥0∞)
    (h : ∀ i, (nativeObject (ThreeGames.object (games i.val) (games (i.val + 1)))).Bounded
      (fun _ => ()) (ε i)) :
    (nativeObject (ThreeGames.object (games 0) (games (length + 1)))).Bounded
      (fun _ => ()) (fun n => ∑ i, ε i n) := by
  have hb := Derivation.bounded (interpretation games) (proof length) ε h
  change (nativeObject (ThreeGames.object (games 0) (games (length + 1)))).Bounded
    (fun _ => ()) (fun n => (Derivation.loss (interpretation games) (proof length)).eval ε n) at hb
  simpa only [loss] using hb

theorem secure (games : Nat → ThreeGames.Game) (length : Nat)
    (h : ∀ i : Fin (length + 1),
      (nativeObject (ThreeGames.object (games i.val) (games (i.val + 1)))).Secure (fun _ => ())) :
    (nativeObject (ThreeGames.object (games 0) (games (length + 1)))).Secure (fun _ => ()) := by
  apply Derivation.sound (P := parameters) (Γ := context (length + 1))
    (S := General.FiniteHybrid.signature games) (interpretation games) (proof length)
  exact h

theorem witnesses_emitted (games : Nat → ThreeGames.Game) (length : Nat) (A)
    (W : (nativeObject (ThreeGames.object (games 0) (games (length + 1)))).Witness
      (fun _ => ()) A) :
    (Derivation.runWitnesses (interpretation games) (proof length) A W).map
      General.CertifiedOutput.emitted = (List.range (length + 1)).map
        (fun i => (i, (⟨Kind.native, W.code⟩ : Sigma system.Code))) := by
  rw [Derivation.runWitnesses_emitted, run]

/-- The full certificate list agrees with the previously selected hybrid
tree, including resources, stopping, realization, and admissibility evidence. -/
theorem witnesses_legacy (games : Nat → ThreeGames.Game) (length : Nat) (A)
    (W : (nativeObject (ThreeGames.object (games 0) (games (length + 1)))).Witness
      (fun _ => ()) A) :
    Derivation.runWitnesses (interpretation games) (proof length) A W =
      (General.FiniteHybrid.analysis games length).runWitnesses A W := by
  unfold Derivation.runWitnesses Presented.Interpretation.runWitnesses
    Presented.Interpretation.analysis General.Derivation.Analysis.runWitnesses
  change (Derivation.tree (interpretation games) (partialProof _ _ _)).extract.map _ = _
  rw [tree_partialProof]
  rfl

/-- A zero-edge comparison is an exact reflexivity path, not an inference
of arbitrary security from an empty list of assumptions. -/
def emptyPath {α : Type} (p : Experiment.Program α) : Experiment.ExactPath p p := .refl p

theorem bounded_zero (game : ThreeGames.Game) :
    (nativeObject (ThreeGames.object game game)).Bounded (fun _ => ()) (fun _ => 0) :=
  General.FiniteHybrid.bounded_zero game

end CryptoLogic.Polygraph.FiniteHybrid
