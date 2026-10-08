import Foundation.Constructions.Symmetric.EncryptThenMAC.RankedExpander
import Foundation.Crypto.Semantics.Machine.OutputAppend
import Foundation.Constructions.Symmetric.BitSampling
import Foundation.Constructions.Symmetric.EncryptThenMAC.SeededGeneratorResources

/-! A genuine arbitrary-width stretching execution with an intentionally
insecure generator: append a public fixed bit to the sampled seed. Local
assertions and ranks derive the expander contract; an exact distinguishing
law prevents mistaking implementation correctness for pseudorandomness. -/
namespace Foundation.Examples.RankedBitExtension
open Machine Foundation.Probability Foundation.Symmetric TimedExecution
open Foundation.Symmetric.EncryptThenMAC SeededGeneratorImplementation
set_option backward.isDefEq.respectTransparency false

def generator (bit : Bool) : Generator where
  seedLength := id
  outputLength := fun width => width + 1
  generate := fun _ seed => Fin.snoc seed bit

theorem generate_toList (bit : Bool) (width : Nat) (seed : Bits width) :
    ((generator bit).generate width seed).toList = seed.toList ++ [bit] := by
  change List.ofFn (Fin.snoc seed bit) = List.ofFn seed ++ [bit]
  rw [List.ofFn_succ_last]
  simp

noncomputable def ranked (bit : Bool) : RankedExpander (generator bit) where
  code := OutputAppend.code bit
  closed := OutputAppend.closed bit
  nonempty := by change 0 < 3; decide
  assertions := fun width seed => OutputAppend.assertions seed.toList
    (seedEntry (generator bit) width seed).inputTape bit
  verified := fun _ seed => OutputAppend.verified seed.toList _ bit
  ranking := fun _ seed => OutputAppend.ranking seed.toList _ bit
  initial := fun width seed => by
    change (OutputAppend.assertions seed.toList (seedEntry (generator bit) width seed).inputTape bit).Holds
      (OutputAppend.initial seed.toList (seedEntry (generator bit) width seed).inputTape)
    exact OutputAppend.initial_valid _ _ _
  cap := fun _ => 3
  bounded := fun _ _ => Nat.le_refl 3
  output := fun width seed machine h => by
    rw [generate_toList bit width seed]
    exact h.2

noncomputable def implementation (bit : Bool) : Expander (generator bit) := (ranked bit).toExpander

theorem fixed_code (bit : Bool) :
    (implementation bit).projected.code = Machine.OneTimePad.keygen.followedBy (OutputAppend.code bit) := rfl

theorem code_length (bit : Bool) : (implementation bit).projected.code.length = 12 := by
  rw [fixed_code]
  simp [Program.followedBy, Machine.OneTimePad.keygen, OutputAppend.code]

theorem budget (bit : Bool) (width : Nat) :
    ((implementation bit).projected.execution width).budget () = 5 * width + 6 := by
  rw [Expander.projected_budget]
  change 5 * width + 3 + 3 = _
  omega

theorem run (bit : Bool) (width horizon : Nat) (hTime : 5 * width + 6 ≤ horizon) :
    (evalConfigWithin ((implementation bit).projected.code)
      (Machine.Configuration.initial (List.replicate width true)) horizon).map
        (SeededGeneratorImplementation.key (generator bit) width) = (generator bit).real width := by
  have hRun := Expander.assembled_run (implementation bit) width horizon
    (by change 5 * width + 3 + 3 ≤ horizon; omega)
  have h := congrArg (fun distribution => distribution.map
    (SeededGeneratorImplementation.key (generator bit) width)) hRun
  exact h.trans ((implementation bit).implements width ())

/-- The visible last bit of every generated output is the fixed public bit. -/
theorem real_last (bit : Bool) (width : Nat) :
    ((generator bit).real width).map (fun bits => bits (Fin.last width)) = PMF.pure bit := by
  simp only [Generator.real, PMF.map_comp, Function.comp_def, generator, Fin.snoc_last]
  change (uniform (Bits width)).map (Function.const (Bits width) bit) = PMF.pure bit
  exact PMF.map_const (uniform (Bits width)) bit

/-- The uniform comparison experiment has a fair last bit at every width. -/
theorem ideal_last (bit : Bool) (width : Nat) :
    ((generator bit).ideal width).map (fun bits => bits (Fin.last width)) = sampleBit :=
  Bits.uniform_last width

/-- Observation of the actual finite-code run, including seed sampling. -/
theorem runtime_last (bit : Bool) (width horizon : Nat) (hTime : 5 * width + 6 ≤ horizon) :
    (evalConfigWithin ((implementation bit).projected.code)
      (Machine.Configuration.initial (List.replicate width true)) horizon).map
        (fun machine => SeededGeneratorImplementation.key (generator bit) width machine
          (Fin.last width)) = PMF.pure bit := by
  have h := congrArg (fun distribution => distribution.map (fun bits => bits (Fin.last width)))
    (run bit width horizon hTime)
  simpa only [PMF.map_comp, Function.comp_def] using h.trans (real_last bit width)

theorem encryption_horizon (bit : Bool) (observerCap : Nat → Nat) (width : Nat) :
    (implementation bit).encryptionHorizon observerCap width =
      55 * width + 96 + observerCap width := by
  change 5 * width + 3 + 3 + 50 * (width + 1) + 40 + observerCap width = _
  omega

/-- These resource conclusions require no pseudorandomness premise. They
count native generation, encryption and the existing two reduction branches. -/
theorem resource_profiles (bit : Bool) (observer : Machine.Program) (observerCap : Nat → Nat)
    (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (implementation bit).generatorBitBound ∧
    PolynomiallyBounded ((implementation bit).encryptionHorizon observerCap) ∧
    PolynomiallyBounded ((implementation bit).encryptionBitBound observer observerCap) ∧
    PolynomiallyBounded (NativeMaskReductionSpaceBackend.bitCap (generator bit) observer observerCap) :=
  (implementation bit).resource_profiles observer observerCap PolynomiallyBounded.id
    (PolynomiallyBounded.const 3)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)) hObserver

/-- Even at width zero the real and ideal experiments have different laws. -/
theorem real_ne_ideal (bit : Bool) (width : Nat) : (generator bit).real width ≠ (generator bit).ideal width := by
  intro h
  have hm := congrArg (fun distribution => distribution.map (fun bits => bits (Fin.last width))) h
  rw [real_last, ideal_last] at hm
  have hp := congrArg (fun distribution : PMF Bool => distribution (!bit)) hm
  have hZero : (PMF.pure bit) (!bit) = 0 := by cases bit <;> simp
  have hSupported : (!bit) ∈ sampleBit.support := PMF.mem_support_uniformOfFintype _
  exact ((PMF.mem_support_iff sampleBit (!bit)).mp hSupported) (hp.symm.trans hZero)

end Foundation.Examples.RankedBitExtension
