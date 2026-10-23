import Foundation.Logic.Polygraph.StructuralCartesianProductTracks

/-! Proof-path comparison by output observations. Product comparison is
reconstructed using the existing eta argument diagram. Unit-valued paths are
compared using existing terminality, exchange, and groupoid diagrams. Atomic
observations remain explicit proof obligations; global coherence is not assumed. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ObservationCoherence
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

private theorem mapIdentity {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    path.map (fun w => w) (fun e => e) = path := by
  induction path <;> simp_all only [Track.map]

private def rightStep {a b : Shape Atom} {p q : Wire a b} (change : Step p q) :
    Homotopy (.comp (.step (.seqLeft change (.identity b))) (.step (.root (.rightId q))))
      (.comp (.step (.root (.rightId p))) (.step change)) :=
  (Four.comp ((CategoryCritical.Context.seqLeft .hole (.identity b)).changeCell change).symm (.refl _)).trans
    (argumentCell (.rightId a b) change)

private def rightTrack {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    Homotopy (.comp (seqLeftTrack (.identity b) path) (.step (.root (.rightId q))))
      (.comp (.step (.root (.rightId p))) path) := by
  have result := FourNaturality.natural (fun w : Wire a b => Wire.seq w (.identity b)) (fun w => w)
    (fun e => Step.seqLeft e (.identity b)) (fun e => e)
    (fun w => Track.step (Step.root (Root.rightId w))) (fun e => rightStep e) path
  simpa only [mapIdentity, seqLeftTrack] using result

private def unitExchange {a : Shape Atom} {p q : Wire a .unit} (path : ProofTrack p q) :
    Homotopy (.comp (seqLeftTrack (.identity .unit) path) (.step (.seqRight q (.root .unitIdentity))))
      (.comp (.step (.seqRight p (.root .unitIdentity))) (seqLeftTrack (.discard .unit) path)) :=
  FourNaturality.natural _ _ (fun e => Step.seqLeft e (.identity .unit)) (fun e => Step.seqLeft e (.discard .unit))
    (fun w => Track.step (Step.seqRight w (Step.root Root.unitIdentity)))
    (fun e => Four.generator (Generator.seqExchange e (.root .unitIdentity))) path

def terminal {a : Shape Atom} (p : Wire a .unit) : ProofTrack p (.discard a) :=
  .comp (.inv (.step (.root (.rightId p))))
    (.comp (.step (.seqRight p (.root .unitIdentity))) (.step (.root (.discardAfter p))))

def terminalContract {a : Shape Atom} {p q : Wire a .unit} (path : ProofTrack p q) :
    Homotopy (.comp path (terminal q)) (terminal p) := by
  have unitSquare : Homotopy
      (.comp path (.inv (.step (.root (.rightId q)))) )
      (.comp (.inv (.step (.root (.rightId p)))) (seqLeftTrack (.identity .unit) path)) :=
    (FourNaturality.invertSquare (.step (.root (.rightId p))) path
      (seqLeftTrack (.identity .unit) path) (.step (.root (.rightId q))) (rightTrack path).symm).symm
  have afterUnit : Homotopy
      (.comp (seqLeftTrack (.identity .unit) path)
        (.comp (.step (.seqRight q (.root .unitIdentity))) (.step (.root (.discardAfter q)))))
      (.comp (.step (.seqRight p (.root .unitIdentity))) (.step (.root (.discardAfter p)))) :=
    (Four.assoc _ _ _).symm.trans
      ((Four.comp (unitExchange path) (.refl _)).trans
        ((Four.assoc _ _ _).trans (Four.comp (.refl _) (Homotopy.discardTrack path))))
  exact (Four.assoc _ _ _).symm.trans
    ((Four.comp unitSquare (.refl _)).trans
      ((Four.assoc _ _ _).trans (Four.comp (.refl _) afterUnit)))

/-- Proof comparison into the terminal output, not cancellation of a wire or
of stochastic observations. The cancelled suffix is a common proof track. -/
def terminalParallel {a : Shape Atom} {p q : Wire a .unit} (first second : ProofTrack p q) : Homotopy first second :=
  Homotopy.cancelRight (terminal q) ((terminalContract first).trans (terminalContract second).symm)

/-- A certificate supplies only the atomic output comparisons. Product nodes
split recursively; terminal nodes need no supplied comparison. -/
def AtomicCertificate {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    (first second : ProofTrack p q) → Type
  | .atom _, _, _, first, second => Homotopy first second
  | .unit, _, _, _, _ => PUnit
  | .pair _ _, _, _, first, second =>
      AtomicCertificate (ProductTracks.firstProjection first) (ProductTracks.firstProjection second) ×
      AtomicCertificate (ProductTracks.secondProjection first) (ProductTracks.secondProjection second)

def reconstruct {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    (first second : ProofTrack p q) → AtomicCertificate first second → Homotopy first second
  | .atom _, _, _, _, _, cell => cell
  | .unit, _, _, first, second, _ => terminalParallel first second
  | .pair _ _, _, _, first, second, certificate =>
      ProductTracks.reflect first second
        (reconstruct _ _ certificate.1) (reconstruct _ _ certificate.2)

def observe {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    {first second : ProofTrack p q} → Homotopy first second → AtomicCertificate first second
  | .atom _, _, _, _, _, cell => cell
  | .unit, _, _, _, _, _ => PUnit.unit
  | .pair b c, _, _, _, _, cell =>
      (observe (cell.whisker (.seqLeft (fst b c))), observe (cell.whisker (.seqLeft (snd b c))))

theorem comparable_iff_atomic {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) :
    Nonempty (Homotopy first second) ↔ Nonempty (AtomicCertificate first second) :=
  ⟨fun ⟨cell⟩ => ⟨observe cell⟩, fun ⟨certificate⟩ => ⟨reconstruct first second certificate⟩⟩

def atomCount : Shape Atom → Nat
  | .atom _ => 1
  | .unit => 0
  | .pair b c => atomCount b + atomCount c

/-- Number of supplied atomic comparison slots, excluding all proof payloads. -/
def certificateLeaves {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    {first second : ProofTrack p q} → AtomicCertificate first second → Nat
  | .atom _, _, _, _, _, _ => 1
  | .unit, _, _, _, _, _ => 0
  | .pair _ _, _, _, _, _, certificate => certificateLeaves certificate.1 + certificateLeaves certificate.2

theorem certificateLeaves_eq {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (certificate : AtomicCertificate first second) : certificateLeaves certificate = atomCount b := by
  induction b with
  | atom => rfl
  | unit => rfl
  | pair b c ih₁ ih₂ => exact congrArg₂ (· + ·) (ih₁ certificate.1) (ih₂ certificate.2)

def NoAtoms : Shape Atom → Prop
  | .atom _ => False
  | .unit => True
  | .pair b c => NoAtoms b ∧ NoAtoms c

def terminalCertificate {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    (first second : ProofTrack p q) → NoAtoms b → AtomicCertificate first second
  | .atom _, _, _, _, _, impossible => False.elim impossible
  | .unit, _, _, _, _, _ => PUnit.unit
  | .pair _ _, _, _, first, second, empty =>
      (terminalCertificate (ProductTracks.firstProjection first) (ProductTracks.firstProjection second) empty.1,
        terminalCertificate (ProductTracks.secondProjection first) (ProductTracks.secondProjection second) empty.2)

def noAtomsCoherent {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q)
    (empty : NoAtoms b) : Homotopy first second :=
  reconstruct first second (terminalCertificate first second empty)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ObservationCoherence
