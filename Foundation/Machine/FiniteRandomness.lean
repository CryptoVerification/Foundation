import Foundation.Machine.Execution
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Prime.Basic

namespace Machine

open Foundation.Probability
open scoped ENNReal

/-- Inspect one transition using a supplied fair bit. At deterministic
instructions and after halt this bit is ignored. This is a mathematical
coupling, not a new instruction or a charge for unused random bits. -/
def stepWithBit (p : Program) (c : Configuration) (bit : Bool) : Configuration :=
  match next p c with
  | none => c
  | some (.inl d) => d
  | some (.inr (d₀, d₁)) => if bit then d₁ else d₀

theorem stepPMF_eq_map_bit (p : Program) (c : Configuration) :
    stepPMF p c = sampleBit.map (stepWithBit p c) := by
  unfold stepPMF stepWithBit
  cases next p c with
  | none => simp [PMF.map_const, Function.const_def]
  | some result =>
      cases result with
      | inl d => simp [PMF.map_const, Function.const_def]
      | inr ds => rfl

/-- One bit per inspected round suffices to describe a bounded run, with
ignored bits padding deterministic transitions and already halted branches. -/
def runWithBits (p : Program) (start : Configuration) :
    (rounds : Nat) → (Fin rounds → Bool) → Configuration
  | 0, _ => start
  | rounds + 1, bits =>
      runWithBits p (stepWithBit p start (bits 0)) rounds (Fin.tail bits)

theorem uniform_map_equiv {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    (uniform α).map e = uniform β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [uniform, Fintype.card_congr e]
  · intro a ha
    simp only [ite_eq_right_iff]
    intro h
    exact False.elim (ha (by simpa using congrArg e.symm h.symm))

private theorem uniform_pair {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (uniform α).bind (fun a => (uniform β).map (fun b => (a, b))) =
      uniform (α × β) := by
  classical
  ext ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, uniform, ENNReal.mul_inv,
    Prod.mk.injEq, ite_and, mul_ite]

private def bitsConsEquiv (rounds : Nat) :
    (Bool × (Fin rounds → Bool)) ≃ (Fin (rounds + 1) → Bool) where
  toFun pair := Fin.cons pair.1 pair.2
  invFun bits := (bits 0, Fin.tail bits)
  left_inv := by intro pair; simp
  right_inv := Fin.cons_self_tail

theorem uniform_bits_cons (rounds : Nat) :
    sampleBit.bind (fun bit => (uniform (Fin rounds → Bool)).map (Fin.cons bit)) =
      uniform (Fin (rounds + 1) → Bool) := by
  have h := congrArg (fun distribution => distribution.map (bitsConsEquiv rounds))
    (uniform_pair (α := Bool) (β := Fin rounds → Bool))
  rw [uniform_map_equiv] at h
  simpa [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
    sampleBit, bitsConsEquiv] using h

/-- The existing operational PMF evaluator is exactly the image of a
uniform finite random tape, including early-halting branches. -/
theorem evalConfigWithin_eq_uniform_bits (p : Program) (start : Configuration)
    (rounds : Nat) :
    evalConfigWithin p start rounds =
      (uniform (Fin rounds → Bool)).map (runWithBits p start rounds) := by
  induction rounds generalizing start with
  | zero => simp [evalConfigWithin, runWithBits, PMF.map_const, Function.const_def]
  | succ rounds ih =>
      conv_lhs => rw [show rounds + 1 = 1 + rounds by omega, evalConfigWithin_add]
      simp only [evalConfigWithin, PMF.pure_bind, stepPMF_eq_map_bit,
        PMF.bind_map, Function.comp_def, ih]
      rw [← uniform_bits_cons, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def, runWithBits, Fin.cons_zero, Fin.tail_cons]

/-- Every event after `rounds` inspections has dyadic probability. The
denominator is `2^rounds`; no termination assumption is needed. -/
theorem evalWithin_event_dyadic (p : Program) (input : List Bool) (rounds : Nat)
    (event : Option (List Bool) → Prop) :
    ∃ count : Nat, eventProb (evalWithin p input rounds) event =
      (count : ℝ≥0∞) / (2 ^ rounds : Nat) := by
  classical
  rw [evalWithin, evalConfigWithin_eq_uniform_bits, PMF.map_comp]
  unfold eventProb
  rw [PMF.toOuterMeasure_map_apply]
  let accepted : Set (Fin rounds → Bool) :=
    (fun bits => if (runWithBits p (Configuration.initial input) rounds bits).halted
      then some (runWithBits p (Configuration.initial input) rounds bits).outputBits
      else none) ⁻¹' {value | event value}
  refine ⟨Fintype.card accepted, ?_⟩
  change (PMF.uniformOfFintype (Fin rounds → Bool)).toOuterMeasure accepted = _
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp

/-- Exact uniform sampling from a finite nonempty type after a fixed finite
budget requires its cardinality to divide a power of two. The decoder may
be arbitrary; permitting invalid codes does not evade this restriction. -/
theorem card_dvd_pow_two_of_exact_uniform {α : Type*} [Fintype α] [Nonempty α]
    (p : Program) (input : List Bool) (rounds : Nat)
    (decode : List Bool → Option α)
    (hUniform : (evalWithin p input rounds).map (fun bits => bits.bind decode) =
      (uniform α).map some) :
    Fintype.card α ∣ 2 ^ rounds := by
  classical
  let a : α := Classical.choice inferInstance
  have hProbability : eventProb (evalWithin p input rounds)
      (fun bits => bits.bind decode = some a) = (Fintype.card α : ℝ≥0∞)⁻¹ := by
    have h := congrArg (fun distribution : PMF (Option α) =>
      eventProb distribution (· = some a)) hUniform
    simpa [eventProb, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply,
      Set.indicator_apply, uniform, eq_comm] using h
  obtain ⟨count, hCount⟩ := evalWithin_event_dyadic p input rounds
    (fun bits => bits.bind decode = some a)
  have hQuotient : (count : ℝ≥0∞) / (2 ^ rounds : Nat) =
      1 / (Fintype.card α : ℝ≥0∞) := by
    simpa using hCount.symm.trans hProbability
  have hCross := (ENNReal.div_eq_div_iff
    (by simp : (Fintype.card α : ℝ≥0∞) ≠ 0)
    (ENNReal.natCast_ne_top _)
    (by simp : ((2 ^ rounds : Nat) : ℝ≥0∞) ≠ 0)
    (ENNReal.natCast_ne_top _)).mp hQuotient
  simp only [mul_one] at hCross
  have hNat : Fintype.card α * count = 2 ^ rounds := by
    exact_mod_cast hCross
  exact ⟨count, hNat.symm⟩

/-- In particular, an odd-prime scalar domain has no exact uniform sampler
at a fixed worst-case budget in the current fair-bit machine. -/
theorem no_exact_uniform_of_odd_prime_card {α : Type*} [Fintype α] [Nonempty α]
    (hPrime : Nat.Prime (Fintype.card α)) (hOdd : Fintype.card α ≠ 2)
    (p : Program) (input : List Bool) (rounds : Nat)
    (decode : List Bool → Option α) :
    (evalWithin p input rounds).map (fun bits => bits.bind decode) ≠
      (uniform α).map some := by
  intro hUniform
  exact hOdd (Nat.prime_eq_prime_of_dvd_pow hPrime Nat.prime_two
    (card_dvd_pow_two_of_exact_uniform p input rounds decode hUniform))

end Machine
