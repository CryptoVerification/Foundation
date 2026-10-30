import Foundation.Crypto.Logic.Polygraph.ApproximateGameProduct

/-! A frame may correlate its retained register with the active game input.
Lifting a path requires preservation of the whole joint law. Conditional
preservation for each register value constructs this obligation locally.
The lift is semantic and does not compile the original path into a machine. -/
namespace CryptoLogic.Polygraph.Experiment.CorrelatedGameFrames
open Foundation.Probability GameCoherence
set_option backward.isDefEq.respectTransparency false
noncomputable section

structure Frame (game : Observed) (C : Type) where
  law : PMF (game.Outcome × C)
  marginal : law.map Prod.fst = game.program.eval

def Frame.observed {game : Observed} {C : Type} (frame : Frame game C) (test : C → Prop) : Observed where
  Outcome := game.Outcome × C
  program := .sample frame.law
  event s := game.event s.1 ∧ test s.2

local instance frameFintype {game : Observed} {C : Type} [Fintype game.Outcome] [Fintype C]
    (frame : Frame game C) (test : C → Prop) : Fintype (frame.observed test).Outcome :=
  inferInstanceAs (Fintype (game.Outcome × C))

def framedKernel {a b : Observed} {C : Type} (path : GameCoherence.Path a b) :
    a.Outcome × C → PMF (b.Outcome × C) := fun s => (path.kernel s.1).map (fun y => (y, s.2))

def Compatible {a b : Observed} {C : Type} (source : Frame a C) (target : Frame b C)
    (path : GameCoherence.Path a b) : Prop := source.law.bind (framedKernel path) = target.law

theorem joint_project {a b : Observed} {C : Type} (source : Frame a C) (path : GameCoherence.Path a b) :
    (source.law.bind (fun s => (framedKernel path s).map (fun t => (s,t)))).map
      (fun pair => (pair.1.1, pair.2.1)) = path.joint := by
  simp only [framedKernel, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have h := congrArg (fun law : PMF a.Outcome =>
    law.bind (fun x => (path.kernel x).map (fun y => (x,y)))) source.marginal
  simpa only [PMF.bind_map, Function.comp_def, Path.joint] using h

def lift {a b : Observed} {C : Type} (source : Frame a C) (target : Frame b C)
    (test : C → Prop) (path : GameCoherence.Path a b) (preserve : Compatible source target path) :
    GameCoherence.Path (source.observed test) (target.observed test) := .step {
  kernel := framedKernel path
  preserve := preserve
  bad pair := mismatch a b (pair.1.1, pair.2.1)
  agree := by
    intro s _ t supported good
    obtain ⟨y, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    subst t
    exact and_congr (Classical.not_not.mp good) Iff.rfl
  loss := path.loss
  bound := by
    have h := eventProb_map
      (source.law.bind (fun s => (framedKernel path s).map (fun t => (s,t))))
      (fun pair => (pair.1.1, pair.2.1)) (mismatch a b)
    rw [joint_project] at h
    exact h.symm.trans_le path.mismatch_bound }

theorem lift_kernel {a b : Observed} {C : Type} (source : Frame a C) (target : Frame b C)
    (test : C → Prop) (path : GameCoherence.Path a b) (preserve : Compatible source target path) :
    (lift source target test path preserve).kernel = framedKernel path := rfl

theorem lift_loss {a b : Observed} {C : Type} (source : Frame a C) (target : Frame b C)
    (test : C → Prop) (path : GameCoherence.Path a b) (preserve : Compatible source target path) :
    (lift source target test path preserve).loss = path.loss := rfl

theorem lift_distance {a b : Observed} {C : Type} [Fintype a.Outcome] [Fintype b.Outcome] [Fintype C]
    (source : Frame a C) (target : Frame b C) (test : C → Prop) (p q : GameCoherence.Path a b)
    (hp : Compatible source target p) (hq : Compatible source target q) :
    FiniteKernelVariation.distance (source.observed test).program.eval
      (lift source target test p hp).kernel (lift source target test q hq).kernel =
      FiniteKernelVariation.distance a.program.eval p.kernel q.kernel := by
  change FiniteKernelVariation.distance source.law (framedKernel p) (framedKernel q) = _
  have h := FiniteKernelVariation.frame_eq source.law Prod.fst Prod.snd p.kernel q.kernel
  rw [source.marginal] at h
  exact h

def liftCell {a b : Observed} {C : Type} [Fintype a.Outcome] [Fintype b.Outcome] [Fintype C]
    (source : Frame a C) (target : Frame b C) (test : C → Prop)
    {p q : GameCoherence.Path a b} {δ} (cell : ApproximateGameCoherence.Cell4 p q δ)
    (hp : Compatible source target p) (hq : Compatible source target q) :
    ApproximateGameCoherence.Cell4 (lift source target test p hp) (lift source target test q hq) δ :=
  .generator ⟨by rw [lift_distance]; exact cell.sound.kernel_bound, cell.sound.loss_eq⟩

def liftExact {a b : Observed} {C : Type}
    (source : Frame a C) (target : Frame b C) (test : C → Prop)
    {p q : GameCoherence.Path a b} (cell : GameCoherence.Cell4 p q)
    (hp : Compatible source target p) (hq : Compatible source target q) :
    GameCoherence.Cell4 (lift source target test p hp) (lift source target test q hq) :=
  .generator ⟨by intro s; change (p.kernel s.1).map _ = (q.kernel s.1).map _
                 rw [cell.sound.kernel_eq], cell.sound.loss_eq⟩

def mixture {game : Observed} {C : Type} (labels : PMF C) (conditional : C → PMF game.Outcome)
    (marginal : labels.bind conditional = game.program.eval) : Frame game C where
  law := labels.bind (fun c => (conditional c).map (fun x => (x,c)))
  marginal := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change labels.bind (fun c => (conditional c).map id) = _
    simpa only [PMF.map_id] using marginal

theorem compatible_of_fibres {a b : Observed} {C : Type} (labels : PMF C)
    (source : C → PMF a.Outcome) (target : C → PMF b.Outcome)
    (hs : labels.bind source = a.program.eval) (ht : labels.bind target = b.program.eval)
    (path : GameCoherence.Path a b) (localPreserve : ∀ c ∈ labels.support, (source c).bind path.kernel = target c) :
    Compatible (mixture labels source hs) (mixture labels target ht) path := by
  unfold Compatible mixture framedKernel
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply bind_congr_of_support
  intro c hc
  rw [← PMF.map_bind, localPreserve c hc]

theorem framed_seq {a b c : Observed} {C : Type}
    (p : GameCoherence.Path a b) (q : GameCoherence.Path b c) (s : a.Outcome × C) :
    framedKernel (.seq p q) s = (framedKernel p s).bind (framedKernel q) := by
  simp only [framedKernel, Path.kernel, PMF.map_bind, PMF.bind_map, Function.comp_def]

theorem compatible_seq {a b c : Observed} {C : Type}
    (source : Frame a C) (middle : Frame b C) (target : Frame c C)
    (p : GameCoherence.Path a b) (q : GameCoherence.Path b c)
    (hp : Compatible source middle p) (hq : Compatible middle target q) :
    Compatible source target (.seq p q) := by
  unfold Compatible at *
  have same : framedKernel (C := C) (.seq p q) = fun s => (framedKernel p s).bind (framedKernel q) :=
    funext (framed_seq p q)
  rw [same, ← PMF.bind_bind, hp, hq]

def liftSeq {a b c : Observed} {C : Type}
    (source : Frame a C) (middle : Frame b C) (target : Frame c C) (test : C → Prop)
    (p : GameCoherence.Path a b) (q : GameCoherence.Path b c)
    (hp : Compatible source middle p) (hq : Compatible middle target q) :
    GameCoherence.Cell4
      (lift source target test (.seq p q) (compatible_seq source middle target p q hp hq))
      (.seq (lift source middle test p hp) (lift middle target test q hq)) :=
  .generator ⟨fun s => framed_seq p q s, rfl⟩

def liftEdit {a b : Observed} {C : Type} [Fintype a.Outcome] [Fintype b.Outcome] [Fintype C]
    (source : Frame a C) (target : Frame b C) (test : C → Prop)
    {d e : GameCoherence.DiagramBridge.Closed a b} {δ}
    (edit : ApproximateDiagramEdits.Edit d e δ)
    (hp : Compatible source target (GameCoherence.DiagramBridge.evaluate d))
    (hq : Compatible source target (GameCoherence.DiagramBridge.evaluate e)) :
    ApproximateDiagramEdits.Edit
      (GameCoherence.DiagramBridge.diagram
        (lift source target test (GameCoherence.DiagramBridge.evaluate d) hp))
      (GameCoherence.DiagramBridge.diagram
        (lift source target test (GameCoherence.DiagramBridge.evaluate e) hq)) δ := by
  apply ApproximateDiagramEdits.Edit.game
  simp only [GameCoherence.DiagramBridge.evaluate_diagram]
  exact liftCell source target test edit.comparison hp hq

/-- Deterministic side information, including a copy of an already sampled
value, is represented by its actual correlated law. -/
def tagged (game : Observed) {C : Type} (tag : game.Outcome → C) : Frame game C where
  law := game.program.eval.map (fun x => (x, tag x))
  marginal := by
    rw [PMF.map_comp]
    exact PMF.map_id _

theorem compatible_tagged {a b : Observed} {C : Type}
    (sourceTag : a.Outcome → C) (targetTag : b.Outcome → C) (path : GameCoherence.Path a b)
    (invariant : ∀ x ∈ a.program.eval.support, ∀ y ∈ (path.kernel x).support,
      targetTag y = sourceTag x) :
    Compatible (tagged a sourceTag) (tagged b targetTag) path := by
  unfold Compatible tagged framedKernel
  simp only [PMF.bind_map, Function.comp_def]
  rw [← path.preserve, PMF.map_bind]
  apply bind_congr_of_support
  intro x hx
  change (path.kernel x).bind (fun y => PMF.pure (y, sourceTag x)) =
    (path.kernel x).bind (fun y => PMF.pure (y, targetTag y))
  apply bind_congr_of_support
  intro y hy
  rw [invariant x hx y hy]

/-- Keeping a full copy of the input and requiring the original diagonal
joint law at the endpoint forces stationarity on reachable inputs. -/
theorem compatible_copy_stationary {a : Observed} (path : GameCoherence.Path a a)
    (preserve : Compatible (tagged a id) (tagged a id) path) :
    ∀ x ∈ a.program.eval.support, path.kernel x = PMF.pure x := by
  intro x hx
  have fixed : ∀ y ∈ (path.kernel x).support, y = x := by
    intro y hy
    have sourceSupported : (x,x) ∈ (tagged a id).law.support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨x,hx,rfl⟩
    have nextSupported : (y,x) ∈ (framedKernel path (x,x)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨y,hy,rfl⟩
    have jointSupported : (y,x) ∈ ((tagged a id).law.bind (framedKernel path)).support :=
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨(x,x),sourceSupported,nextSupported⟩
    rw [preserve] at jointSupported
    obtain ⟨z,_,same⟩ := (PMF.mem_support_map_iff _ _ _).mp jointSupported
    exact (congrArg Prod.fst same).symm.trans (congrArg Prod.snd same)
  calc
    path.kernel x = (path.kernel x).bind PMF.pure := (PMF.bind_pure _).symm
    _ = (path.kernel x).bind (fun _ => PMF.pure x) := by
      apply bind_congr_of_support
      intro y hy
      rw [fixed y hy]
    _ = PMF.pure x := PMF.bind_const _ _

end
end CryptoLogic.Polygraph.Experiment.CorrelatedGameFrames
