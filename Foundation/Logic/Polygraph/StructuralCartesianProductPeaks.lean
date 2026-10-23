import Foundation.Logic.Polygraph.StructuralCartesianProductTriangleCoherence
import Foundation.Logic.Polygraph.StructuralCartesianCategoryPeaks

/-! Constructive resolutions for four explicitly typed beta/eta overlap
sites, and their reversals. These are actual Cartesian.Step boundaries;
arbitrary coinitial eighteen-rule steps are not classified by this interface. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive Peak : {a b : Shape Atom} → Wire a b → Wire a b → Wire a b → Type where
  | fst {a b c} (p : Wire a (.pair b c)) :
      Peak (.seq (fork (.seq p (Cartesian.fst b c)) (.seq p (Cartesian.snd b c))) (Cartesian.fst b c)) (.seq p (Cartesian.fst b c)) (.seq p (Cartesian.fst b c))
  | snd {a b c} (p : Wire a (.pair b c)) :
      Peak (.seq (fork (.seq p (Cartesian.fst b c)) (.seq p (Cartesian.snd b c))) (Cartesian.snd b c)) (.seq p (Cartesian.snd b c)) (.seq p (Cartesian.snd b c))
  | forkFirst {a b c} (p : Wire a b) (q : Wire a c) :
      Peak (fork (.seq (fork p q) (Cartesian.fst b c)) (.seq (fork p q) (Cartesian.snd b c))) (fork p q) (fork p (.seq (fork p q) (Cartesian.snd b c)))
  | forkLast {a b c} (p : Wire a b) (q : Wire a c) :
      Peak (fork (.seq (fork p q) (Cartesian.fst b c)) (.seq (fork p q) (Cartesian.snd b c))) (fork p q) (fork (.seq (fork p q) (Cartesian.fst b c)) q)
  | swap {a b} {p q r : Wire a b} (child : Peak p q r) : Peak p r q

def Peak.steps {a b : Shape Atom} {p q r : Wire a b} : Peak p q r → Step p q × Step p r
  | .fst p => ⟨.seqLeft (.root (.eta p)) (Cartesian.fst _ _),
      .root (.betaFst (.seq p (Cartesian.fst _ _)) (.seq p (Cartesian.snd _ _)))⟩
  | .snd p => ⟨.seqLeft (.root (.eta p)) (Cartesian.snd _ _),
      .root (.betaSnd (.seq p (Cartesian.fst _ _)) (.seq p (Cartesian.snd _ _)))⟩
  | .forkFirst p q => ⟨.root (.eta (fork p q)), ProductCritical.forkFirst p q⟩
  | .forkLast p q => ⟨.root (.eta (fork p q)),
      .seqRight (.copy _) (.tensorRight (.seq (fork p q) (Cartesian.fst _ _)) (.root (.betaSnd p q)))⟩
  | .swap child => ⟨child.steps.2, child.steps.1⟩

def Peak.first {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) : Step p q := peak.steps.1
def Peak.second {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) : Step p r := peak.steps.2

structure Resolution {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) where
  target : Wire a b
  firstTail : ProofTrack q target
  secondTail : ProofTrack r target
  family : Fin 3
  first_bound : stepCount (.comp (.step peak.first) firstTail) ≤ 2
  second_bound : stepCount (.comp (.step peak.second) secondTail) ≤ 2
  first_forward : CategoryCritical.Forward firstTail
  second_forward : CategoryCritical.Forward secondTail
  cell : Cell (.comp (.step peak.first) firstTail) (.comp (.step peak.second) secondTail)

def resolve {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) : Resolution peak := by
  match peak with
  | .fst p =>
      exact ⟨_, .refl _, .refl _, 0, by change 1 ≤ 2; decide, by change 1 ≤ 2; decide,
        True.intro, True.intro, .comp (fstCell p) (.refl _)⟩
  | .snd p =>
      exact ⟨_, .refl _, .refl _, 1, by change 1 ≤ 2; decide, by change 1 ≤ 2; decide,
        True.intro, True.intro, .comp (sndCell p) (.refl _)⟩
  | .forkFirst p q =>
      exact ⟨_, .refl _, .step (ProductCritical.forkLast p q), 2,
        by change 1 ≤ 2; decide, by change 2 ≤ 2; decide, True.intro, True.intro,
        (Four.rightUnit _).trans (forkCell p q).symm⟩
  | .forkLast p q =>
      exact ⟨_, .refl _, .step (.seqRight (.copy _) (.tensorLeft (.root (.betaFst p q)) q)), 2,
        by change 1 ≤ 2; decide, by change 2 ≤ 2; decide, True.intro, True.intro,
        (Four.rightUnit _).trans (forkOtherOrder p q).symm⟩
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

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical
