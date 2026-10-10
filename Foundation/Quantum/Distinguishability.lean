import Foundation.Quantum.Effects
import Mathlib.Tactic.Linarith

/-! Operational, auxiliary-system-complete indistinguishability. The error is
an acceptance-probability bound; no unproved trace/diamond-norm identity is used. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Kraus
variable {a b c : Space}

theorem amplify_seq (K : Kraus a b) (L : Kraus b c) (e : Space) :
    (K.seq L).amplify e = (K.amplify e).seq (L.amplify e) := by
  have hop : (fun p : K.index × L.index =>
      Op.tensor (L.operator p.2 * K.operator p.1) (Op.ident e)) =
      (fun p : K.index × L.index => Op.tensor (L.operator p.2) (Op.ident e) *
        Op.tensor (K.operator p.1) (Op.ident e)) := by
    funext p
    simpa [Op.seq, Op.ident] using
      Op.tensor_seq (K.operator p.1) (L.operator p.2) (Op.ident e) (Op.ident e)
  exact congrArg (fun f => (⟨K.index × L.index, inferInstance, f⟩ :
    Kraus (.tensor a e) (.tensor c e))) hop

end Kraus

namespace Channel
variable {a b c : Space}

theorem seq_run_matrix (C : Channel a b) (D : Channel b c) (ρ : Density a) :
    ((C.seq D).run ρ).matrix = (D.run (C.run ρ)).matrix :=
  C.toKraus.seq_apply D.toKraus ρ.matrix

theorem amplify_seq_run_matrix (C : Channel a b) (D : Channel b c) (e : Space)
    (ρ : Density (.tensor a e)) :
    (((C.seq D).amplify e).run ρ).matrix =
      ((D.amplify e).run ((C.amplify e).run ρ)).matrix := by
  change ((C.toKraus.seq D.toKraus).amplify e).apply ρ.matrix = _
  rw [Kraus.amplify_seq, Kraus.seq_apply]
  rfl

end Channel

/-- Universally quantified finite auxiliary systems may be entangled with the input. -/
def Approx {a b : Space} (C D : Channel a b) (ε : ℝ) : Prop :=
  ∀ (e : Space) (ρ : Density (.tensor a e)) (E : Effect (.tensor b e)),
    |E.probability ((C.amplify e).run ρ) - E.probability ((D.amplify e).run ρ)| ≤ ε

/-- A single-use quantum distinguisher with a private auxiliary register. -/
structure Adversary (a b : Space) where
  auxiliary : Space
  input : Density (.tensor a auxiliary)
  test : Effect (.tensor b auxiliary)

def Adversary.acceptance {a b} (A : Adversary a b) (C : Channel a b) : ℝ :=
  A.test.probability ((C.amplify A.auxiliary).run A.input)

theorem approx_iff_adversaries {a b} (C D : Channel a b) (ε : ℝ) :
    Approx C D ε ↔ ∀ A : Adversary a b, |A.acceptance C - A.acceptance D| ≤ ε := by
  constructor
  · intro h A
    exact h A.auxiliary A.input A.test
  · intro h e ρ E
    exact h ⟨e, ρ, E⟩

namespace Approx
variable {a b c : Space} {C D F : Channel a b} {ε δ : ℝ}

theorem refl (C : Channel a b) : Approx C C 0 := by
  intro e ρ E
  simp

theorem symm (h : Approx C D ε) : Approx D C ε := by
  intro e ρ E
  simpa only [abs_sub_comm] using h e ρ E

theorem mono (h : Approx C D ε) (hε : ε ≤ δ) : Approx C D δ :=
  fun e ρ E => (h e ρ E).trans hε

theorem trans (h : Approx C D ε) (k : Approx D F δ) : Approx C F (ε + δ) := by
  intro e ρ E
  exact (abs_sub_le _ _ _).trans (add_le_add (h e ρ E) (k e ρ E))

/-- Arbitrary physical processing after the challenge cannot increase this error. -/
theorem post (h : Approx C D ε) (P : Channel b c) :
    Approx (C.seq P) (D.seq P) ε := by
  intro e ρ E
  have hc : E.probability (((C.seq P).amplify e).run ρ) =
      ((P.amplify e).pullEffect E).probability ((C.amplify e).run ρ) := by
    unfold Effect.probability
    rw [Channel.amplify_seq_run_matrix]
    exact congrArg Complex.re ((P.amplify e).toKraus.trace_dual _ _)
  have hd : E.probability (((D.seq P).amplify e).run ρ) =
      ((P.amplify e).pullEffect E).probability ((D.amplify e).run ρ) := by
    unfold Effect.probability
    rw [Channel.amplify_seq_run_matrix]
    exact congrArg Complex.re ((P.amplify e).toKraus.trace_dual _ _)
  rw [hc, hd]
  exact h e ρ _

/-- Arbitrary physical preparation before the challenge is also permitted. -/
theorem pre {x : Space} (h : Approx C D ε) (P : Channel x a) :
    Approx (P.seq C) (P.seq D) ε := by
  intro e ρ E
  have hc : E.probability (((P.seq C).amplify e).run ρ) =
      E.probability ((C.amplify e).run ((P.amplify e).run ρ)) := by
    unfold Effect.probability
    rw [Channel.amplify_seq_run_matrix]
  have hd : E.probability (((P.seq D).amplify e).run ρ) =
      E.probability ((D.amplify e).run ((P.amplify e).run ρ)) := by
    unfold Effect.probability
    rw [Channel.amplify_seq_run_matrix]
  rw [hc, hd]
  exact h e ((P.amplify e).run ρ) E

theorem seq {P Q : Channel b c} (h : Approx C D ε) (k : Approx P Q δ) :
    Approx (C.seq P) (D.seq Q) (ε + δ) :=
  (h.post P).trans (k.pre D)

end Approx
end
end Foundation.Quantum
