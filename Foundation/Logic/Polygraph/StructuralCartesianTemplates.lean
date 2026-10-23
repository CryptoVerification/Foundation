import Foundation.Logic.Polygraph.StructuralCartesianRewriting

/-! Typed substitution templates for local cartesian diagrams. A template may
contain zero, one or several occurrences of the SAME wire argument. Replacement
returns actual contextual rewrite tracks, not an arbitrary path generator. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
open TypedRouting
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive Template (input output : Shape Atom) : Shape Atom → Shape Atom → Type where
  | hole : Template input output input output
  | fixed {a b} (wire : Wire a b) : Template input output a b
  | seq {a b c} : Template input output a b → Template input output b c → Template input output a c
  | tensor {a b c d} : Template input output a b → Template input output c d → Template input output (.pair a c) (.pair b d)

namespace Template

def apply {input output : Shape Atom} : {a b : Shape Atom} → Template input output a b → Wire input output → Wire a b
  | _, _, .hole, wire => wire
  | _, _, .fixed wireFixed, _ => wireFixed
  | _, _, .seq first second, wire => .seq (first.apply wire) (second.apply wire)
  | _, _, .tensor first second, wire => .tensor (first.apply wire) (second.apply wire)

def holes {input output : Shape Atom} : {a b : Shape Atom} → Template input output a b → Nat
  | _, _, .hole => 1
  | _, _, .fixed _ => 0
  | _, _, .seq first second | _, _, .tensor first second => first.holes + second.holes

def pair {input output a b c : Shape Atom} (first : Template input output a b) (second : Template input output a c) :
    Template input output a (.pair b c) := .seq (.fixed (.copy a)) (.tensor first second)

def change {input output : Shape Atom} {p q : Wire input output} (step : Step p q) :
    {a b : Shape Atom} → (template : Template input output a b) → ProofTrack (template.apply p) (template.apply q)
  | _, _, .hole => .step step
  | _, _, .fixed wireFixed => .refl wireFixed
  | _, _, .seq first second =>
      .comp (seqLeftTrack (second.apply p) (change step first)) (seqRightTrack (first.apply q) (change step second))
  | _, _, .tensor first second =>
      .comp (tensorLeftTrack (second.apply p) (change step first)) (tensorRightTrack (first.apply q) (change step second))

end Template

def stepCount {a b : Shape Atom} : {p q : Wire a b} → ProofTrack p q → Nat
  | _, _, .refl _ => 0
  | _, _, .step _ => 1
  | _, _, .comp first second => stepCount first + stepCount second
  | _, _, .inv child => stepCount child

/-- Track syntax-tree constructors; Step payload/context and Wire sizes are
excluded. Unlike stepCount this includes refl, comp and inverse nodes. -/
def trackConstructorCount {a b : Shape Atom} : {p q : Wire a b} → ProofTrack p q → Nat
  | _, _, .refl _ | _, _, .step _ => 1
  | _, _, .comp first second => 1 + trackConstructorCount first + trackConstructorCount second
  | _, _, .inv child => 1 + trackConstructorCount child

theorem stepCount_map {a b c d : Shape Atom} (f : Wire a b → Wire c d)
    (mapStep : ∀ {p q}, Step p q → Step (f p) (f q)) {p q : Wire a b} (path : ProofTrack p q) :
    stepCount (path.map f mapStep) = stepCount path := by
  induction path <;> simp_all only [Track.map, stepCount]

theorem Template.change_count {input output a b : Shape Atom} {p q : Wire input output}
    (step : Step p q) (template : Template input output a b) : stepCount (template.change step) = template.holes := by
  induction template <;> simp_all only [Template.change, Template.holes, stepCount,
    seqLeftTrack, seqRightTrack, tensorLeftTrack, tensorRightTrack, stepCount_map]

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
