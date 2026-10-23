import Foundation.Logic.Polygraph.StructuralCartesianDistributionCritical
import Foundation.Logic.Polygraph.StructuralCartesianCategoryPeaks

/-! Actual typed distribution/projection overlap resolution, in either
component and either branch order. This interface does not recognize every
arbitrary coinitial pair of Cartesian steps. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.DistributionCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive Peak : {a b : Shape Atom} → Wire a b → Wire a b → Wire a b → Type where
  | fst {a b c d} (p : Wire a b) (q : Wire b c) (r : Wire b d) :
      Peak (.seq (.seq p (fork q r)) (fst c d))
        (.seq (fork (.seq p q) (.seq p r)) (fst c d)) (.seq p (.seq (fork q r) (fst c d)))
  | snd {a b c d} (p : Wire a b) (q : Wire b c) (r : Wire b d) :
      Peak (.seq (.seq p (fork q r)) (snd c d))
        (.seq (fork (.seq p q) (.seq p r)) (snd c d)) (.seq p (.seq (fork q r) (snd c d)))
  | swap {a b} {p q r : Wire a b} (child : Peak p q r) : Peak p r q

def Peak.steps {a b : Shape Atom} {p q r : Wire a b} : Peak p q r → Step p q × Step p r
  | .fst p q r => ⟨.seqLeft (.root (.forkAfter p q r)) (Cartesian.fst _ _), .root (.assoc p (fork q r) (Cartesian.fst _ _))⟩
  | .snd p q r => ⟨.seqLeft (.root (.forkAfter p q r)) (Cartesian.snd _ _), .root (.assoc p (fork q r) (Cartesian.snd _ _))⟩
  | .swap child => ⟨child.steps.2, child.steps.1⟩

def Peak.first {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) : Step p q := peak.steps.1
def Peak.second {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) : Step p r := peak.steps.2

structure Resolution {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) where
  target : Wire a b
  firstTail : ProofTrack q target
  secondTail : ProofTrack r target
  family : Fin 2
  first_bound : stepCount (.comp (.step peak.first) firstTail) ≤ 2
  second_bound : stepCount (.comp (.step peak.second) secondTail) ≤ 2
  first_forward : CategoryCritical.Forward firstTail
  second_forward : CategoryCritical.Forward secondTail
  cell : Cell (.comp (.step peak.first) firstTail) (.comp (.step peak.second) secondTail)

def resolve {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) : Resolution peak := by
  match peak with
  | .fst p q r =>
      exact ⟨_, .step (.root (.betaFst (.seq p q) (.seq p r))), .step (.seqRight p (.root (.betaFst q r))), 0,
        by change 2 ≤ 2; decide, by change 2 ≤ 2; decide, True.intro, True.intro, fstCell p q r⟩
  | .snd p q r =>
      exact ⟨_, .step (.root (.betaSnd (.seq p q) (.seq p r))), .step (.seqRight p (.root (.betaSnd q r))), 1,
        by change 2 ≤ 2; decide, by change 2 ≤ 2; decide, True.intro, True.intro, sndCell p q r⟩
  | .swap child =>
      let result := resolve child
      exact ⟨result.target, result.secondTail, result.firstTail, result.family,
        result.second_bound, result.first_bound, result.second_forward, result.first_forward, result.cell.symm⟩

theorem resolve_bounded {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) :
    stepCount (.comp (.step peak.first) (resolve peak).firstTail) ≤ 2 ∧
      stepCount (.comp (.step peak.second) (resolve peak).secondTail) ≤ 2 :=
  ⟨(resolve peak).first_bound, (resolve peak).second_bound⟩

theorem resolve_forward {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) :
    CategoryCritical.Forward (resolve peak).firstTail ∧ CategoryCritical.Forward (resolve peak).secondTail :=
  ⟨(resolve peak).first_forward, (resolve peak).second_forward⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.DistributionCritical
