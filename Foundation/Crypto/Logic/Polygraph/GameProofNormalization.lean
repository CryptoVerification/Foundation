import Foundation.Crypto.Logic.Polygraph.GameProofHigher

/-! Directed, terminating game-proof normalization. Local branching diagrams
are supplied only for pairs of outgoing atomic steps. Global comparisons are
constructed by rank recursion and pasting, with no inverse game execution.
This is a coherence construction for a specified terminating presentation,
not a finite presentation or a novelty claim. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Vertex Atom Requirement Budget RelatorId : Type} [DecidableEq Requirement]
set_option backward.isDefEq.respectTransparency false

structure Transition (layout : Layout Vertex Atom Requirement Budget) (a b : Vertex) where
  label : Atom
  source_eq : layout.source label = a
  target_eq : layout.target label = b

def Transition.atom {layout : Layout Vertex Atom Requirement Budget} (label : Atom) :
    Transition layout (layout.source label) (layout.target label) := ⟨label, rfl, rfl⟩

def Transition.plan {layout : Layout Vertex Atom Requirement Budget} {a b : Vertex}
    (step : Transition layout a b) : Plan layout a b := by
  rcases step with ⟨label, rfl, rfl⟩
  exact .atom label

inductive Next (layout : Layout Vertex Atom Requirement Budget) (sink : Vertex) : Vertex → Type where
  | done : Next layout sink sink
  | step (label : Atom) : Next layout sink (layout.source label)

/-- A decreasing rank and a deterministic choice of the next atomic step.
Every stopped vertex is the one specified terminal vertex. -/
structure Strategy (layout : Layout Vertex Atom Requirement Budget) (sink : Vertex) where
  rank : Vertex → Nat
  decreases : ∀ label, rank (layout.target label) < rank (layout.source label)
  terminal : ∀ label, layout.source label ≠ sink
  next : ∀ vertex, Next layout sink vertex

def Strategy.normal {layout : Layout Vertex Atom Requirement Budget} {sink : Vertex}
    (strategy : Strategy layout sink) (vertex : Vertex) : Plan layout vertex sink :=
  match strategy.next vertex with
  | .done => .identity sink
  | .step label => .seq (.atom label) (strategy.normal (layout.target label))
termination_by strategy.rank vertex
decreasing_by exact strategy.decreases _

omit [DecidableEq Requirement] in
theorem Strategy.normal_step {layout : Layout Vertex Atom Requirement Budget} {sink : Vertex}
    (strategy : Strategy layout sink) (label : Atom)
    (selected : strategy.next (layout.source label) = .step label) :
    strategy.normal (layout.source label) = .seq (.atom label) (strategy.normal (layout.target label)) := by
  rw [Strategy.normal, selected]

omit [DecidableEq Requirement] in
theorem Strategy.normal_sink {layout : Layout Vertex Atom Requirement Budget} {sink : Vertex}
    (strategy : Strategy layout sink) : strategy.normal sink = .identity sink := by
  cases selected : strategy.next sink with
  | done => rw [Strategy.normal, selected]
  | step label => exact False.elim (strategy.terminal label rfl)

omit [DecidableEq Requirement] in
theorem Plan.rank_le {layout : Layout Vertex Atom Requirement Budget} {sink : Vertex}
    (strategy : Strategy layout sink) {a b : Vertex} (plan : Plan layout a b) :
    strategy.rank b ≤ strategy.rank a := by
  induction plan with
  | identity => exact Nat.le_refl _
  | atom label => exact Nat.le_of_lt (strategy.decreases label)
  | seq _ _ first second => exact second.trans first

omit [DecidableEq Requirement] in
theorem Transition.rank_lt {layout : Layout Vertex Atom Requirement Budget} {sink : Vertex}
    (strategy : Strategy layout sink) {a b : Vertex} (step : Transition layout a b) :
    strategy.rank b < strategy.rank a := by
  rcases step with ⟨label, rfl, rfl⟩
  exact strategy.decreases label

/-- A local branching is joined by directed residual paths and an actual
diagram in the existing catalog. There is no arbitrary-parallel-path root.
No bound or finiteness of the supplied residuals is implicit. -/
structure LocalDiamond (layout : Layout Vertex Atom Requirement Budget) (relators : RelatorId → Relator layout)
    {a b c : Vertex} (first : Transition layout a b) (second : Transition layout a c) where
  join : Vertex
  left : Plan layout b join
  right : Plan layout c join
  cell : Cell layout relators (.seq first.plan left) (.seq second.plan right)

/-- Extend atomic normalization comparisons to a whole plan below a strict
rank bound. The recursion follows the supplied plan, not all possible paths. -/
def foldNormalization {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {sink : Vertex} (strategy : Strategy layout sink) (bound : Nat)
    (atomic : ∀ {a b} (step : Transition layout a b), strategy.rank a < bound →
      Cell layout relators (.seq step.plan (strategy.normal b)) (strategy.normal a)) :
    {a b : Vertex} → (plan : Plan layout a b) → strategy.rank a < bound →
      Cell layout relators (.seq plan (strategy.normal b)) (strategy.normal a)
  | _, _, .identity _, _ => .leftUnit _
  | _, _, .atom label, below => atomic (.atom label) below
  | _, _, .seq first second, below =>
      .trans (.assoc first second _)
        (.trans (.seq (.refl first)
          (foldNormalization strategy bound atomic second (lt_of_le_of_lt (first.rank_le strategy) below)))
          (foldNormalization strategy bound atomic first below))

/-- Normalize an atomic step by resolving it against the strategy's selected
step. Recursive comparisons start strictly below the original source rank. -/
def normalizeTransition {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {sink : Vertex} (strategy : Strategy layout sink)
    (diamonds : ∀ {a b c} (first : Transition layout a b) (second : Transition layout a c),
      LocalDiamond layout relators first second) :
    {a b : Vertex} → (step : Transition layout a b) →
      Cell layout relators (.seq step.plan (strategy.normal b)) (strategy.normal a)
  | a, b, step => by
    cases selected : strategy.next a with
    | done =>
      exact False.elim (strategy.terminal step.label step.source_eq)
    | step chosen =>
      rw [strategy.normal_step chosen selected]
      let peak := diamonds step (.atom chosen)
      let fold : {u v : Vertex} → (path : Plan layout u v) →
          strategy.rank u < strategy.rank (layout.source chosen) →
          Cell layout relators (.seq path (strategy.normal v)) (strategy.normal u) :=
        fun path below => foldNormalization strategy (strategy.rank (layout.source chosen))
          (fun edge below => normalizeTransition strategy diamonds edge) path below
      have first := fold peak.left (step.rank_lt strategy)
      have second := fold peak.right (strategy.decreases chosen)
      exact .trans (.seq (.refl step.plan) first.symm)
        (.trans (.symm (.assoc step.plan peak.left _))
          (.trans (.seq peak.cell (.refl (strategy.normal peak.join)))
            (.trans (.assoc (.atom chosen) peak.right _)
              (.seq (.refl (.atom chosen)) second))))
termination_by a _ _ => strategy.rank a
decreasing_by
  subst_vars
  exact below

/-- Generate the comparison between a completed arbitrary plan and the
computed strategy route. It uses the local diamonds via rank recursion. -/
def normalizePlan {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {sink : Vertex} (strategy : Strategy layout sink)
    (diamonds : ∀ {a b c} (first : Transition layout a b) (second : Transition layout a c),
      LocalDiamond layout relators first second) {a b : Vertex} (plan : Plan layout a b) :
    Cell layout relators (.seq plan (strategy.normal b)) (strategy.normal a) :=
  foldNormalization strategy (strategy.rank a + 1)
    (fun step _ => normalizeTransition strategy diamonds step) plan (Nat.lt_succ_self _)

/-- Complete two parallel plans by the same computed terminal route before
comparing them. The common suffix is deliberately NOT cancelled. -/
def completedCoherence {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {sink : Vertex} (strategy : Strategy layout sink)
    (diamonds : ∀ {a b c} (first : Transition layout a b) (second : Transition layout a c),
      LocalDiamond layout relators first second) {a b : Vertex} (first second : Plan layout a b) :
    Cell layout relators (.seq first (strategy.normal b)) (.seq second (strategy.normal b)) :=
  .trans (normalizePlan strategy diamonds first) (.symm (normalizePlan strategy diamonds second))

def normalizeTerminal {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {sink : Vertex} (strategy : Strategy layout sink)
    (diamonds : ∀ {a b c} (first : Transition layout a b) (second : Transition layout a c),
      LocalDiamond layout relators first second) {a : Vertex} (plan : Plan layout a sink) :
    Cell layout relators plan (strategy.normal a) :=
  .trans (.symm (.rightUnit plan)) (by
    simpa only [strategy.normal_sink] using normalizePlan strategy diamonds plan)

/-- Construct the comparison for any two plans ending at the specified
terminal game. Input plans may have arbitrary identity/association syntax. -/
def terminalCoherence {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {sink : Vertex} (strategy : Strategy layout sink)
    (diamonds : ∀ {a b c} (first : Transition layout a b) (second : Transition layout a c),
      LocalDiamond layout relators first second) {a : Vertex} (first second : Plan layout a sink) :
    Cell layout relators first second :=
  .trans (normalizeTerminal strategy diamonds first) (.symm (normalizeTerminal strategy diamonds second))

omit [DecidableEq Requirement] in
theorem terminal_coherence_complete {layout : Layout Vertex Atom Requirement Budget} {relators : RelatorId → Relator layout}
    {sink : Vertex} (strategy : Strategy layout sink)
    (diamonds : ∀ {a b c} (first : Transition layout a b) (second : Transition layout a c),
      LocalDiamond layout relators first second) {a : Vertex} (first second : Plan layout a sink) :
    Nonempty (Cell layout relators first second) :=
  ⟨terminalCoherence strategy diamonds first second⟩

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
