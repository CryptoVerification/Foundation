import Foundation.Crypto.Logic.General.Execution

/-! Extensional comparison of certified computational reductions. It retains
the instance/adversary family, emitted code, resource certificate, and actual
advantage transformer. It asserts no coupling of the challenge distributions.
Compiler syntax can differ by association and identities. -/
namespace CryptoLogic.General
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {K : CodeSystem} {m n k l : K.Machine}
  {X : SecurityObject.{0, 0} K m} {Y : SecurityObject.{0, 0} K n}
  {Z : SecurityObject.{0, 0} K k} {V : SecurityObject.{0, 0} K l}

def SecurityObject.Packet (X : SecurityObject.{0, 0} K m) :=
  Σ F : InstanceFamily X.goal, Σ A : AdversaryFamily X.goal F, X.Witness F A

def CertifiedReduction.runPacket (reduction : CertifiedReduction X Y) (packet : X.Packet) : Y.Packet :=
  ⟨reduction.reduction.mapFamily packet.1, reduction.reduction.mapAdversaryFamily packet.1 packet.2.1,
    reduction.mapWitness packet.1 packet.2.1 packet.2.2⟩

structure CertifiedComparison (first second : CertifiedReduction X Y) : Prop where
  families : ∀ F, first.reduction.mapFamily F = second.reduction.mapFamily F
  packets : ∀ packet, first.runPacket packet = second.runPacket packet
  programs : ∀ code, first.compiler.run code = second.compiler.run code
  loss : ∀ n ε, first.reduction.loss.eval n ε = second.reduction.loss.eval n ε

namespace CertifiedComparison

theorem refl (reduction : CertifiedReduction X Y) : CertifiedComparison reduction reduction :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem symm {first second : CertifiedReduction X Y} (comparison : CertifiedComparison first second) :
    CertifiedComparison second first :=
  ⟨fun F => (comparison.families F).symm, fun p => (comparison.packets p).symm,
    fun code => (comparison.programs code).symm, fun n ε => (comparison.loss n ε).symm⟩

theorem trans {first second third : CertifiedReduction X Y}
    (one : CertifiedComparison first second) (two : CertifiedComparison second third) :
    CertifiedComparison first third :=
  ⟨fun F => (one.families F).trans (two.families F), fun p => (one.packets p).trans (two.packets p),
    fun code => (one.programs code).trans (two.programs code), fun n ε => (one.loss n ε).trans (two.loss n ε)⟩

theorem comp {first first' : CertifiedReduction X Y} {second second' : CertifiedReduction Y Z}
    (one : CertifiedComparison first first') (two : CertifiedComparison second second') :
    CertifiedComparison (first.comp second) (first'.comp second') := by
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

theorem assoc (first : CertifiedReduction X Y) (second : CertifiedReduction Y Z)
    (third : CertifiedReduction Z V) :
    CertifiedComparison ((first.comp second).comp third) (first.comp (second.comp third)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem leftUnit (reduction : CertifiedReduction X Y) :
    CertifiedComparison ((CertifiedReduction.id X).comp reduction) reduction :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem rightUnit (reduction : CertifiedReduction X Y) :
    CertifiedComparison (reduction.comp (CertifiedReduction.id Y)) reduction :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem resources {first second : CertifiedReduction X Y} (comparison : CertifiedComparison first second)
    (F A) (witness : X.Witness F A) :
    (first.mapWitness F A witness).resources = (second.mapWitness F A witness).resources :=
  congrArg (fun packet : Y.Packet => packet.2.2.resources) (comparison.packets ⟨F, A, witness⟩)

end CertifiedComparison
end CryptoLogic.General
