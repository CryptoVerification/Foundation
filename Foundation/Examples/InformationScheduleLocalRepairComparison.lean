import Foundation.Examples.InformationScheduleLocalRepair
import Foundation.Examples.RandomFunctionMACInformationSchedule

/-! Fair local-repair comparison and an arbitrary-size schedule at the actual
MAC prefix. The number counted is registry-dependent obligations, not elapsed
time, kernel proof size, or changed machine instructions. -/
namespace CryptoOracle.InformationSchedule.LocalRepairComparison
open Foundation.Probability
open LocalRepair
variable {Variable Key : Type} [DecidableEq Variable] [DecidableEq Key]

theorem diagram_repair_iff (old new : Key → Finset Variable) (changed : Finset Key)
    (agree : ∀ key ∉ changed, old key = new key) (seen : Finset Variable)
    (word target : List (Action Variable Key)) (positions : List Nat) (checks : List (Check Variable Key))
    (compiled : compile seen word positions = some (target, checks))
    (accepted : Certificate.validates old seen word target positions = true) :
    Certificate.validates new seen word target positions = true ↔
      (checks.filter (Check.affected changed)).all (Check.holds new) = true := by
  rw [Example.validates_eq] at accepted ⊢
  exact repaired_validates_iff old new changed agree seen word target positions checks compiled accepted

def newSignature (key : Bool) : Finset Bool := if key then {false} else {true}

theorem agrees_except : ∀ key ∉ ({false} : Finset Bool), Example.signature key = newSignature key := by
  intro key unchanged
  cases key <;> simp_all [Example.signature, newSignature]

def source (n : Nat) : List (Action Bool Bool) :=
  [.reveal true, .commit false, .reveal false] ++ List.replicate n (.commit true)

def target (n : Nat) : List (Action Bool Bool) :=
  [.reveal true, .reveal false, .commit false] ++ List.replicate n (.commit true)

def checks (n : Nat) : List (Check Bool Bool) :=
  [.available false {true}] ++ List.replicate n (.available true {false, true}) ++ [.absent false false]

private theorem repeated_sourceChecks (n : Nat) :
    sourceChecks ({false, true} : Finset Bool) (List.replicate n (.commit true)) =
      List.replicate n (.available true {false, true}) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, sourceChecks, ih]

theorem compiled (n : Nat) : compile ∅ (source n) [1] = some (target n, checks n) := by
  simp [compile, replayPlan, swapPlan, source, target, checks, sourceChecks,
    exchangeChecks, repeated_sourceChecks]

theorem old_checks (n : Nat) : (checks n).all (Check.holds Example.signature) = true := by
  simp [checks, Check.holds, Example.signature]

theorem old_accepted (n : Nat) : Certificate.validates Example.signature ∅ (source n) (target n) [1] = true := by
  rw [Example.validates_eq]
  exact (compiled_validates_iff Example.signature ∅ (source n) (target n) [1] (checks n) (compiled n)).mpr
    (old_checks n)

theorem affected_checks (n : Nat) :
    (checks n).filter (Check.affected {false}) = [.available false {true}, .absent false false] := by
  simp [checks, Check.affected]

theorem rechecked (n : Nat) :
    ((checks n).filter (Check.affected {false})).all (Check.holds newSignature) = true := by
  rw [affected_checks]
  decide_cbv

theorem repaired (n : Nat) : Certificate.validates newSignature ∅ (source n) (target n) [1] = true := by
  exact (diagram_repair_iff Example.signature newSignature {false} agrees_except ∅
    (source n) (target n) [1] (checks n) (compiled n) (old_accepted n)).mpr (rechecked n)

theorem exact_counts (n : Nat) :
    (checks n).length = n + 2 ∧ ((checks n).filter (Check.affected {false})).length = 2 := by
  rw [affected_checks]
  constructor
  · simp only [checks, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
    omega
  · rfl

/-- Updating the dependency to the crossed variable invalidates this SAME
script. Local repair is a criterion, not an unconditional acceptance rule. -/
def badSignature (key : Bool) : Finset Bool := if key then {false} else {false, true}

theorem rejects_changed_dependency (n : Nat) :
    Certificate.validates badSignature ∅ (source n) (target n) [1] = false := by
  rw [Example.validates_eq]
  have law := compiled_validates_iff badSignature ∅ (source n) (target n) [1] (checks n) (compiled n)
  have invalid : (checks n).all (Check.holds badSignature) = false := by
    simp [checks, Check.holds, badSignature]
  cases result : Baseline.validates badSignature ∅ (source n) (target n) [1] with
  | false => rfl
  | true => have impossible := law.mp result; rw [invalid] at impossible; contradiction

end CryptoOracle.InformationSchedule.LocalRepairComparison

namespace Foundation.Symmetric.RandomFunctionMACLocalRepair
open Foundation.Probability
open CryptoOracle CryptoOracle.InformationSchedule
open InformationSchedule.LocalRepairComparison
open RandomFunctionMACCausalRepair

noncomputable def policy : (key : Bool) → ({v // v ∈ newSignature key} → Bool) → PMF Bool
  | false, inputs => PMF.pure (inputs ⟨true, by decide⟩)
  | true, inputs => PMF.pure (!(inputs ⟨false, by decide⟩))

noncomputable def joint (word : List (Action Bool Bool)) :
    PMF (PrefixOutcome × InformationSchedule.State Bool Bool Bool) :=
  (firstProgram.run RandomOracle.oracle []).bind fun out =>
    (run newSignature policy word (Example.initial (challenge out.result.2))).map fun final => (out, final)

theorem repaired_joint (n : Nat) : joint (source n) = joint (target n) := by
  unfold joint
  simp_rw [Certificate.validates_kernel newSignature policy ∅ (source n) (target n) [1] (repaired n)]

theorem ordinary_repaired_joint (n : Nat) : joint (source n) = joint (target n) := by
  have old := (LocalRepair.compiled_validates_iff Example.signature ∅ (source n) (target n) [1]
    (checks n) (compiled n)).mpr (old_checks n)
  have accepted := (LocalRepair.repaired_validates_iff Example.signature newSignature {false}
    agrees_except ∅ (source n) (target n) [1] (checks n) (compiled n) old).mpr (rechecked n)
  unfold joint
  simp_rw [Baseline.validated_kernel newSignature policy ∅ (source n) (target n) [1] accepted]

theorem repaired_continuation {Result : Type} (n : Nat)
    (next : PrefixOutcome × InformationSchedule.State Bool Bool Bool → PMF Result) :
    (joint (source n)).bind next = (joint (target n)).bind next := by
  rw [repaired_joint]

theorem continued_game (word : List (Action Bool Bool)) :
    ((joint word).bind fun pair => continuation pair.1) =
      RandomFunctionMACNativeCaller.target.run RandomOracle.oracle [] := by
  rw [← actual_prefix, Program.run_bind]
  simp only [joint, PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_const]
  rfl

end Foundation.Symmetric.RandomFunctionMACLocalRepair
