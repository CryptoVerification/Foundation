import Foundation.Crypto.Logic.Polygraph.GameCoherence

/-! The composed conditional kernel itself, rather than an unrelated endpoint
coupling, witnesses the accumulated event-disagreement bound. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence
open Foundation.Probability
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

def mismatch (a b : Observed.{u}) (pair : a.Outcome × b.Outcome) : Prop :=
  ¬(a.event pair.1 ↔ b.event pair.2)

theorem Step.mismatch_bound {a b : Observed.{u}} (transition : Step a b) :
    eventProb transition.joint (mismatch a b) ≤ transition.loss := by
  apply le_trans (eventProb_mono_of_support _ ?_) transition.bound
  intro pair reachable different
  obtain ⟨x, hx, reachable⟩ := (PMF.mem_support_bind_iff _ _ _).mp reachable
  obtain ⟨y, hy, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reachable
  subst pair
  by_contra good
  exact different (transition.agree x hx y hy good)

namespace Path
def triple {a b c : Observed.{u}} (p : Path a b) (q : Path b c) :
    PMF (a.Outcome × b.Outcome × c.Outcome) :=
  a.program.eval.bind fun x => (p.kernel x).bind fun y =>
    (q.kernel y).map fun z => (x, y, z)

theorem triple_left {a b c : Observed.{u}} (p : Path a b) (q : Path b c) :
    (triple p q).map (fun t => (t.1, t.2.1)) = p.joint := by
  simp only [triple, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (a.program.eval.bind fun x => (p.kernel x).bind fun y =>
    (q.kernel y).map (Function.const c.Outcome (x, y))) = _
  simp only [PMF.map_const]
  rfl

theorem triple_right {a b c : Observed.{u}} (p : Path a b) (q : Path b c) :
    (triple p q).map (fun t => (t.2.1, t.2.2)) = q.joint := by
  simp only [triple, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (a.program.eval.bind fun x => (p.kernel x).bind fun y =>
    (q.kernel y).map (fun z => (y, z))) = _
  rw [← PMF.bind_bind, p.preserve]
  rfl

theorem triple_endpoints {a b c : Observed.{u}} (p : Path a b) (q : Path b c) :
    (triple p q).map (fun t => (t.1, t.2.2)) = (p.seq q).joint := by
  simp only [triple, joint, kernel, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- The original input and final state, coupled by the actual composed
transition kernel, disagree about success with probability at most the loss. -/
theorem mismatch_bound {a b : Observed.{u}} (path : Path a b) :
    eventProb path.joint (mismatch a b) ≤ path.loss := by
  induction path with
  | identity game =>
      have empty : eventProb (Path.identity game).joint (mismatch game game) = 0 := by
        simp only [joint, kernel, PMF.pure_map]
        change eventProb (game.program.eval.map (fun x => (x, x))) _ = 0
        rw [eventProb_map]
        simp [mismatch, eventProb]
      exact le_of_eq empty
  | step transition => exact transition.mismatch_bound
  | seq p q ihp ihq =>
      rw [← triple_endpoints p q, eventProb_map]
      calc
        _ ≤ eventProb (triple p q) (fun t => mismatch _ _ (t.1, t.2.1) ∨
            mismatch _ _ (t.2.1, t.2.2)) := by
          apply eventProb_mono_of_support
          intro t _ different
          classical
          by_cases first : mismatch _ _ (t.1, t.2.1)
          · exact Or.inl first
          · right
            intro second
            exact different ((not_not.mp first).trans second)
        _ ≤ eventProb (triple p q) (fun t => mismatch _ _ (t.1, t.2.1)) +
            eventProb (triple p q) (fun t => mismatch _ _ (t.2.1, t.2.2)) := eventProb_or_le _ _ _
        _ = eventProb p.joint (mismatch _ _) + eventProb q.joint (mismatch _ _) := by
          have hl := eventProb_map (triple p q) (fun t => (t.1, t.2.1)) (mismatch _ _)
          have hr := eventProb_map (triple p q) (fun t => (t.2.1, t.2.2)) (mismatch _ _)
          rw [triple_left] at hl
          rw [triple_right] at hr
          exact congrArg₂ (· + ·) hl.symm hr.symm
        _ ≤ _ := add_le_add ihp ihq

end Path
end
end CryptoLogic.Polygraph.Experiment.GameCoherence
