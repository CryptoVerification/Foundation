import Foundation.Examples.GameProofPRGComputational

/-! A concrete orientation boundary: the registered native-to-masking
compiler used by the PRG proof has no reverse compiler in this CodeSystem.
This is a theorem about the current registry, not all possible machines. -/
namespace CryptoLogic.General.Backends.OrientationBoundary
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

theorem masking_closed : {source target : Kind} → (compiler : Compiler system source target) →
    source = .masking → target = .masking
  | _, _, .identity _, same => same
  | _, _, .primitive primitive, same => by cases primitive <;> cases same
  | _, _, .comp first second, same => masking_closed second (masking_closed first same)

theorem no_reverse_compiler : ¬ Nonempty (Compiler system .masking .native) := by
  rintro ⟨compiler⟩
  have impossible := masking_closed compiler rfl
  cases impossible

theorem no_reverse_reduction (G : Generator) (time : Nat → Nat) (side : Bool) :
    ¬ Nonempty (CertifiedReduction
      (Generator.Polygraph.object G time .prg)
      (Generator.Polygraph.object G time (.half side))) := by
  rintro ⟨reduction⟩
  exact no_reverse_compiler ⟨reduction.compiler⟩

theorem forward_exists_no_reverse (G : Generator) (time : Nat → Nat) (side : Bool) :
    Nonempty (CertifiedReduction
      (Generator.Polygraph.object G time (.half side))
      (Generator.Polygraph.object G time .prg)) ∧
    ¬ Nonempty (CertifiedReduction
      (Generator.Polygraph.object G time .prg)
      (Generator.Polygraph.object G time (.half side))) :=
  ⟨⟨(Generator.Polygraph.uniformRewrite G time side).comp
      (Generator.Polygraph.replacement G time side)⟩, no_reverse_reduction G time side⟩

end CryptoLogic.General.Backends.OrientationBoundary
