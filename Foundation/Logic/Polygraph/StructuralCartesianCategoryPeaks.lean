import Foundation.Logic.Polygraph.StructuralCartesianCategoryCritical

/-! Typed classification and resolution of root/root and rigid proper-site
peaks for association and the two units. Variable-site and separated overlaps
are handled by existing argument/exchange diagrams, not classified here.
Other cartesian roots, including unitIdentity, are outside this fragment. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CategoryCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive RootRule : {a b : Shape Atom} → Wire a b → Wire a b → Type where
  | assoc {a b c d} (p : Wire a b) (q : Wire b c) (r : Wire c d) :
      RootRule (.seq (.seq p q) r) (.seq p (.seq q r))
  | leftUnit {a b} (p : Wire a b) : RootRule (.seq (.identity a) p) p
  | rightUnit {a b} (p : Wire a b) : RootRule (.seq p (.identity b)) p

def RootRule.step {a b : Shape Atom} {p q : Wire a b} : RootRule p q → Step p q
  | .assoc p q r => associate p q r
  | .leftUnit p => CategoryCritical.leftUnit p
  | .rightUnit p => CategoryCritical.rightUnit p

def RootRule.view {a b : Shape Atom} {p q : Wire a b} : Cartesian.Root p q → Option (RootRule p q)
  | .assoc p q r => some (.assoc p q r)
  | .leftId p => some (.leftUnit p)
  | .rightId p => some (.rightUnit p)
  | _ => none

theorem RootRule.view_complete {a b : Shape Atom} {p q : Wire a b} (root : Cartesian.Root p q)
    (member : root.code.val < 3) :
    ∃ selected : RootRule p q, RootRule.view root = some selected ∧ selected.step = .root root := by
  cases root with
  | assoc p q r => exact ⟨.assoc _ _ _, rfl, rfl⟩
  | leftId p => exact ⟨.leftUnit _, rfl, rfl⟩
  | rightId p => exact ⟨.rightUnit _, rfl, rfl⟩
  | _ => simp only [Cartesian.Root.code] at member; omega

/-- The proper rigid sites in these three source patterns are the left
composition node of association and the fixed identity of either unit.
An arbitrary argument is intentionally not a rigid site. -/
inductive Peak : {a b : Shape Atom} → Wire a b → Wire a b → Wire a b → Type where
  | roots {a b} {p q r : Wire a b} (first : RootRule p q) (second : RootRule p r) : Peak p q r
  | assocNested {a b c d} (p : Wire a b) (q : Wire b c) (r : Wire c d)
      {target : Wire a c} (inner : RootRule (.seq p q) target) :
      Peak (.seq (.seq p q) r) (.seq p (.seq q r)) (.seq target r)
  | leftNested {a b} (p : Wire a b) {target : Wire a a} (inner : RootRule (.identity a) target) :
      Peak (.seq (.identity a) p) p (.seq target p)
  | rightNested {a b} (p : Wire a b) {target : Wire b b} (inner : RootRule (.identity b) target) :
      Peak (.seq p (.identity b)) p (.seq p target)

def Peak.first {a b : Shape Atom} {p q r : Wire a b} : Peak p q r → Step p q
  | .roots first _ => first.step
  | .assocNested p q r _ => associate p q r
  | .leftNested p _ => leftUnit p
  | .rightNested p _ => rightUnit p

def Peak.second {a b : Shape Atom} {p q r : Wire a b} : Peak p q r → Step p r
  | .roots _ second => second.step
  | .assocNested _ _ r inner => .seqLeft inner.step r
  | .leftNested p inner => .seqLeft inner.step p
  | .rightNested p inner => .seqRight p inner.step

def Forward {a b : Shape Atom} : {p q : Wire a b} → ProofTrack p q → Prop
  | _, _, .refl _ | _, _, .step _ => True
  | _, _, .comp first second => Forward first ∧ Forward second
  | _, _, .inv _ => False

structure Resolution {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) where
  target : Wire a b
  firstTail : ProofTrack q target
  secondTail : ProofTrack r target
  family : Option (Fin 5)
  first_bound : stepCount (.comp (.step peak.first) firstTail) ≤ 3
  second_bound : stepCount (.comp (.step peak.second) secondTail) ≤ 3
  first_forward : Forward firstTail
  second_forward : Forward secondTail
  cell : Cell (.comp (.step peak.first) firstTail) (.comp (.step peak.second) secondTail)

/-- Five nontrivial schematic families: pentagon, left/middle/right unit
over association, and the two units at identity. Equal root applications need
no critical generator. This is constructive, including both root orientations. -/
def resolve {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) : Resolution peak := by
  cases peak with
  | roots first second =>
      cases first with
      | assoc p q r =>
          cases second with
          | assoc p q r => exact ⟨_, .refl _, .refl _, none, by change 1 ≤ 3; omega, by change 1 ≤ 3; omega, by change True; exact True.intro, by change True; exact True.intro, .refl _⟩
          | rightUnit p =>
              exact ⟨_, .step (.seqRight _ (rightUnit _)), .refl _, some ⟨3, by decide⟩, by change 2 ≤ 3; omega, by change 1 ≤ 3; omega, by change True; exact True.intro, by change True; exact True.intro,
                (rightUnitCell _ _).trans (Four.rightUnit _).symm⟩
      | leftUnit p =>
          cases second with
          | leftUnit p => exact ⟨_, .refl _, .refl _, none, by change 1 ≤ 3; omega, by change 1 ≤ 3; omega, by change True; exact True.intro, by change True; exact True.intro, .refl _⟩
          | rightUnit p =>
              exact ⟨_, .refl _, .refl _, some ⟨4, by decide⟩, by change 1 ≤ 3; omega, by change 1 ≤ 3; omega, by change True; exact True.intro, by change True; exact True.intro, Four.comp (unitCell _) (.refl _)⟩
      | rightUnit p =>
          cases second with
          | rightUnit p => exact ⟨_, .refl _, .refl _, none, by change 1 ≤ 3; omega, by change 1 ≤ 3; omega, by change True; exact True.intro, by change True; exact True.intro, .refl _⟩
          | assoc p q r =>
              exact ⟨_, .refl _, .step (.seqRight _ (rightUnit _)), some ⟨3, by decide⟩, by change 1 ≤ 3; omega, by change 2 ≤ 3; omega, by change True; exact True.intro, by change True; exact True.intro,
                (Four.rightUnit _).trans (rightUnitCell _ _).symm⟩
          | leftUnit p =>
              exact ⟨_, .refl _, .refl _, some ⟨4, by decide⟩, by change 1 ≤ 3; omega, by change 1 ≤ 3; omega, by change True; exact True.intro, by change True; exact True.intro, Four.comp (unitCell _).symm (.refl _)⟩
  | assocNested p q r inner =>
      cases inner with
      | assoc p q r =>
          exact ⟨_, .step (associate _ _ _), two (associate _ _ _) (.seqRight _ (associate _ _ _)),
            some ⟨0, by decide⟩, by change 2 ≤ 3; omega, by change 3 ≤ 3; omega, by change True; exact True.intro, by change True ∧ True; exact ⟨True.intro, True.intro⟩, pentagonCell _ _ _ _⟩
      | leftUnit p =>
          exact ⟨_, .step (leftUnit _), .refl _, some ⟨1, by decide⟩, by change 2 ≤ 3; omega, by change 1 ≤ 3; omega, by change True; exact True.intro, by change True; exact True.intro,
            (leftUnitCell _ _).trans (Four.rightUnit _).symm⟩
      | rightUnit p =>
          exact ⟨_, .step (.seqRight _ (leftUnit _)), .refl _, some ⟨2, by decide⟩, by change 2 ≤ 3; omega, by change 1 ≤ 3; omega, by change True; exact True.intro, by change True; exact True.intro,
            (middleUnitCell _ _).trans (Four.rightUnit _).symm⟩
  | leftNested p inner => cases inner
  | rightNested p inner => cases inner

theorem resolve_bounded {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) :
    stepCount (.comp (.step peak.first) (resolve peak).firstTail) ≤ 3 ∧
      stepCount (.comp (.step peak.second) (resolve peak).secondTail) ≤ 3 :=
  ⟨(resolve peak).first_bound, (resolve peak).second_bound⟩

theorem resolve_forward {a b : Shape Atom} {p q r : Wire a b} (peak : Peak p q r) :
    Forward (resolve peak).firstTail ∧ Forward (resolve peak).secondTail :=
  ⟨(resolve peak).first_forward, (resolve peak).second_forward⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CategoryCritical
