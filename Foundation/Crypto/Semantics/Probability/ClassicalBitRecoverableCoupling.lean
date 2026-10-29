import Foundation.Crypto.Semantics.Probability.ClassicalBitRoundtripKernel
import Foundation.Crypto.Semantics.Probability.KernelRecovery

/-! A different maximal coupling on the same sharp edge. Integer masses
partition the target keys by their source, so a deterministic reverse recovers
every source bit. This changes the selected forward kernel, not the endpoint
cipher laws. The finite index types encode the reachable native state sets. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable
open Foundation.Probability
open scoped BigOperators ENNReal
noncomputable section

abbrev Result := Fin 5 × Bool

def sourceResult (message bit : Bool) : Result := if bit then (2,!message) else (0,message)
def parent (key : Fin 5) : Bool := decide (key = 2 ∨ key = 4)
def targetResult (message : Bool) (key : Fin 5) : Result := (key, if parent key then !message else message)

def counts (bit : Bool) (key : Fin 5) : ℕ :=
  if bit then (if key = 2 then 94 else if key = 4 then 34 else 0)
  else (if key = 0 then 88 else if key = 1 then 20 else if key = 3 then 20 else 0)

theorem counts_sum (bit : Bool) : ∑ key, counts bit key = 128 := by
  cases bit <;> decide +kernel

def forward (bit : Bool) : PMF (Fin 5) := PMF.ofFintype
  (fun key => ENNReal.ofReal ((counts bit key : ℝ) / 128)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun key _ => by positivity), ← Finset.sum_div, ← Nat.cast_sum, counts_sum]
    norm_num)

theorem forward_real (bit : Bool) (key : Fin 5) :
    (forward bit key).toReal = (counts bit key : ℝ) / 128 := ENNReal.toReal_ofReal (by positivity)

def sourceLaw : PMF Bool := uniform Bool

theorem source_real (bit : Bool) : (sourceLaw bit).toReal = 1 / 2 := by
  norm_num [sourceLaw, uniform, PMF.uniformOfFintype_apply]

def targetLaw : PMF (Fin 5) := sourceLaw.bind forward

theorem singleton {A : Type} (law : PMF A) (a : A) : eventProb law (· = a) = law a :=
  PMF.toOuterMeasure_apply_singleton law a

theorem map_real {A B : Type} [Fintype A] [DecidableEq B] (law : PMF A) (f : A → B) (b : B) :
    ((law.map f) b).toReal = ∑ a, if f a = b then (law a).toReal else 0 := by
  classical
  rw [← singleton, eventProb_map, event_real_sum]

theorem target_real (key : Fin 5) :
    (targetLaw key).toReal = ((counts false key + counts true key : ℕ) : ℝ) / 256 := by
  rw [← singleton]
  unfold targetLaw
  rw [event_bind_real]
  simp only [singleton, source_real, forward_real, Fintype.sum_bool, Nat.cast_add]
  ring

theorem source_law (message : Bool) : sourceLaw.map (sourceResult message) = Roundtrip.p message := by
  classical
  ext result
  apply (ENNReal.toReal_eq_toReal_iff' ((sourceLaw.map (sourceResult message)).apply_ne_top result)
    ((Roundtrip.p message).apply_ne_top result)).mp
  rw [map_real, Roundtrip.p_real]
  rcases result with ⟨key, ciphertext⟩
  fin_cases key <;> cases message <;> cases ciphertext <;>
    norm_num [sourceResult, source_real, Fintype.sum_bool, Roundtrip.sourceCount, Fin.ext_iff]

theorem target_law (message : Bool) : targetLaw.map (targetResult message) = Roundtrip.q message := by
  classical
  ext result
  apply (ENNReal.toReal_eq_toReal_iff' ((targetLaw.map (targetResult message)).apply_ne_top result)
    ((Roundtrip.q message).apply_ne_top result)).mp
  rw [map_real, Roundtrip.q_real]
  rcases result with ⟨key, ciphertext⟩
  simp only [targetResult, Prod.mk.injEq, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases key <;> cases message <;> cases ciphertext <;>
    norm_num [parent, target_real, counts, Fin.ext_iff, Roundtrip.targetCount]

theorem counts_compatible (bit : Bool) (key : Fin 5) : counts bit key ≠ 0 → parent key = bit := by
  cases bit <;> fin_cases key <;> decide +kernel

theorem parent_supported (bit : Bool) (key : Fin 5) (supported : key ∈ (forward bit).support) : parent key = bit := by
  apply counts_compatible bit key
  intro zero
  have hr : (forward bit key).toReal = 0 := by rw [forward_real, zero]; norm_num
  have hp : forward bit key = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp hr |>.resolve_right ((forward bit).apply_ne_top key)
  exact (PMF.mem_support_iff _ _).mp supported hp

theorem recovers (bit : Bool) : (forward bit).map parent = PMF.pure bit := by
  change ((forward bit).bind (fun key => PMF.pure (parent key))) = _
  calc
    _ = (forward bit).bind (fun _ => PMF.pure bit) := by
      apply bind_congr_of_support
      intro key supported
      rw [parent_supported bit key supported]
    _ = _ := PMF.bind_const _ _

theorem reverse_preserves : targetLaw.map parent = sourceLaw := by
  unfold targetLaw
  rw [PMF.map_bind]
  simp only [recovers, PMF.bind_pure]

theorem result_agrees (message bit : Bool) (key : Fin 5)
    (same : key = (sourceResult message bit).1) : targetResult message key = sourceResult message bit := by
  subst key
  cases bit <;> simp [targetResult, sourceResult, parent]

def bad (pair : Bool × Fin 5) : Prop := pair.2 ≠ if pair.1 then (2 : Fin 5) else 0

instance badDecidable (pair : Bool × Fin 5) : Decidable (bad pair) := by
  unfold bad
  infer_instance

def joint : PMF (Bool × Fin 5) := sourceLaw.bind fun bit => (forward bit).map fun key => (bit,key)

def badCount (bit : Bool) (key : Fin 5) : ℕ := if bad (bit,key) then counts bit key else 0

theorem badCount_sum : (∑ bit, ∑ key, badCount bit key) = 74 := by decide +kernel

theorem bad_real : (eventProb joint bad).toReal = 37 / 128 := by
  classical
  unfold joint
  rw [event_bind_real]
  simp only [eventProb_map, event_real_sum, source_real, forward_real]
  have h (bit : Bool) (key : Fin 5) :
      (if bad (bit,key) then (counts bit key : ℝ) / 128 else 0) = (badCount bit key : ℝ) / 128 := by
    by_cases good : bad (bit,key) <;> simp [badCount, good]
  simp_rw [h, ← Finset.sum_div]
  have hrow (bit : Bool) : (1 / 2 : ℝ) * ((∑ key, (badCount bit key : ℝ)) / 128) =
      (∑ key, (badCount bit key : ℝ)) / 256 := by ring
  simp_rw [hrow]
  rw [← Finset.sum_div]
  have hc : (∑ bit, ∑ key, (badCount bit key : ℝ)) = 74 := by exact_mod_cast badCount_sum
  rw [hc]
  norm_num

theorem bad_probability : eventProb joint bad = (37 / 128 : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_of_lt ((eventProb_le_one joint bad).trans_lt (by simp)))
    (ENNReal.div_ne_top (by simp) (by norm_num))).mp
  rw [bad_real]
  norm_num

def reverseBad (pair : Fin 5 × Bool) : Prop := bad (pair.2,pair.1)
instance reverseBadDecidable (pair : Fin 5 × Bool) : Decidable (reverseBad pair) := by
  unfold reverseBad
  infer_instance

def reverseJoint : PMF (Fin 5 × Bool) := targetLaw.map (fun key => (key,parent key))
def reverseCount (key : Fin 5) : ℕ :=
  if reverseBad (key,parent key) then counts false key + counts true key else 0

theorem reverseCount_sum : (∑ key, reverseCount key) = 74 := by decide +kernel

theorem reverse_bad_real : (eventProb reverseJoint reverseBad).toReal = 37 / 128 := by
  classical
  rw [reverseJoint, eventProb_map, event_real_sum]
  simp only [target_real]
  have h (key : Fin 5) :
      (if reverseBad (key,parent key) then ((counts false key + counts true key : ℕ) : ℝ) / 256 else 0) =
        (reverseCount key : ℝ) / 256 := by
    by_cases good : reverseBad (key,parent key) <;> simp [reverseCount, good]
  simp_rw [h]
  rw [← Finset.sum_div, ← Nat.cast_sum, reverseCount_sum]
  norm_num

theorem reverse_bad_probability : eventProb reverseJoint reverseBad = (37 / 128 : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_of_lt ((eventProb_le_one reverseJoint reverseBad).trans_lt (by simp)))
    (ENNReal.div_ne_top (by simp) (by norm_num))).mp
  rw [reverse_bad_real]
  norm_num

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.Recoverable
