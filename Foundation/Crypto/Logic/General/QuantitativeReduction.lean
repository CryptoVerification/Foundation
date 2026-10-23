import Foundation.Crypto.Meta.General.ResourceSecurity
import Foundation.Crypto.Logic.Polygraph.ComputationalComparison

/-! Finite quantitative reductions with actual code and execution evidence.
Unlike CertifiedReduction, constant statistical errors are permitted. Secure
asymptotic transport requires an explicit promotion proof. -/
namespace CryptoLogic.General
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {K : CodeSystem} {m n k l : K.Machine}
  {X : SecurityObject.{0, 0} K m} {Y : SecurityObject.{0, 0} K n}
  {Z : SecurityObject.{0, 0} K k} {V : SecurityObject.{0, 0} K l}

structure QuantitativeReduction (X : SecurityObject.{0, 0} K m) (Y : SecurityObject.{0, 0} K n) where
  reduction : Reduction X.goal Y.goal
  compiler : Compiler K m n
  mapWitness : ∀ F A, X.Witness F A →
    Y.Witness (reduction.mapFamily F) (reduction.mapAdversaryFamily F A)
  code_eq : ∀ F A W, (mapWitness F A W).code = compiler.run W.code

namespace QuantitativeReduction

def toTransform (T : QuantitativeReduction X Y) : CertifiedTransform X Y where
  transform := ⟨T.reduction.mapInstance, T.reduction.reduce⟩
  compiler := T.compiler
  mapWitness := T.mapWitness
  code_eq := T.code_eq

def id (X : SecurityObject.{0, 0} K m) : QuantitativeReduction X X where
  reduction := Reduction.id X.goal
  compiler := .identity m
  mapWitness := fun _ _ W => W
  code_eq := by intros; rfl

def comp (first : QuantitativeReduction X Y) (second : QuantitativeReduction Y Z) :
    QuantitativeReduction X Z where
  reduction := first.reduction.comp second.reduction
  compiler := .comp first.compiler second.compiler
  mapWitness := fun F A W => second.mapWitness _ _ (first.mapWitness F A W)
  code_eq := by intros; rw [second.code_eq, first.code_eq]; rfl

def ofCertified (T : CertifiedReduction X Y) : QuantitativeReduction X Y :=
  ⟨T.reduction, T.compiler, T.mapWitness, T.code_eq⟩

def promote (T : QuantitativeReduction X Y) (negligible : T.reduction.loss.PreservesNegligible) :
    CertifiedReduction X Y := ⟨T.reduction, T.compiler, T.mapWitness, T.code_eq, negligible⟩

theorem promote_ofCertified (T : CertifiedReduction X Y) :
    (ofCertified T).promote T.negligible = T := by cases T; rfl

def runPacket (T : QuantitativeReduction X Y) (packet : X.Packet) : Y.Packet :=
  ⟨T.reduction.mapFamily packet.1, T.reduction.mapAdversaryFamily packet.1 packet.2.1,
    T.mapWitness packet.1 packet.2.1 packet.2.2⟩

theorem bounded (T : QuantitativeReduction X Y) (F epsilon)
    (hypothesis : Y.Bounded (T.reduction.mapFamily F) epsilon) :
    X.Bounded F (fun n => T.reduction.loss.eval n (epsilon n)) := by
  intro A admissible n
  exact (T.reduction.advantageProfile_le F A n).trans
    (T.reduction.loss.monotone n (hypothesis _ (T.toTransform.admissible F A admissible) n))

end QuantitativeReduction

structure QuantitativeComparison (first second : QuantitativeReduction X Y) : Prop where
  families : ∀ F, first.reduction.mapFamily F = second.reduction.mapFamily F
  packets : ∀ packet, first.runPacket packet = second.runPacket packet
  programs : ∀ code, first.compiler.run code = second.compiler.run code
  loss : ∀ n epsilon, first.reduction.loss.eval n epsilon = second.reduction.loss.eval n epsilon

namespace QuantitativeComparison

theorem refl (reduction : QuantitativeReduction X Y) : QuantitativeComparison reduction reduction :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem symm {first second : QuantitativeReduction X Y} (comparison : QuantitativeComparison first second) :
    QuantitativeComparison second first :=
  ⟨fun F => (comparison.families F).symm, fun p => (comparison.packets p).symm,
    fun code => (comparison.programs code).symm, fun n ε => (comparison.loss n ε).symm⟩

theorem trans {first second third : QuantitativeReduction X Y}
    (one : QuantitativeComparison first second) (two : QuantitativeComparison second third) :
    QuantitativeComparison first third :=
  ⟨fun F => (one.families F).trans (two.families F), fun p => (one.packets p).trans (two.packets p),
    fun code => (one.programs code).trans (two.programs code), fun n ε => (one.loss n ε).trans (two.loss n ε)⟩

theorem comp {first first' : QuantitativeReduction X Y} {second second' : QuantitativeReduction Y Z}
    (one : QuantitativeComparison first first') (two : QuantitativeComparison second second') :
    QuantitativeComparison (first.comp second) (first'.comp second') := by
  constructor
  · intro F
    exact (congrArg second.reduction.mapFamily (one.families F)).trans (two.families _)
  · intro packet
    change second.runPacket (first.runPacket packet) = second'.runPacket (first'.runPacket packet)
    rw [one.packets, two.packets]
  · intro code
    change second.compiler.run (first.compiler.run code) = second'.compiler.run (first'.compiler.run code)
    rw [one.programs, two.programs]
  · intro n ε
    exact (one.loss n (second.reduction.loss.eval n ε)).trans
      (congrArg (first'.reduction.loss.eval n) (two.loss n ε))

theorem assoc (first : QuantitativeReduction X Y) (second : QuantitativeReduction Y Z)
    (third : QuantitativeReduction Z V) :
    QuantitativeComparison ((first.comp second).comp third) (first.comp (second.comp third)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem leftUnit (reduction : QuantitativeReduction X Y) :
    QuantitativeComparison ((QuantitativeReduction.id X).comp reduction) reduction :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem rightUnit (reduction : QuantitativeReduction X Y) :
    QuantitativeComparison (reduction.comp (QuantitativeReduction.id Y)) reduction :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem resources {first second : QuantitativeReduction X Y} (comparison : QuantitativeComparison first second)
    (F A) (witness : X.Witness F A) :
    (first.mapWitness F A witness).resources = (second.mapWitness F A witness).resources :=
  congrArg (fun packet : Y.Packet => packet.2.2.resources) (comparison.packets ⟨F, A, witness⟩)

end QuantitativeComparison

end CryptoLogic.General
