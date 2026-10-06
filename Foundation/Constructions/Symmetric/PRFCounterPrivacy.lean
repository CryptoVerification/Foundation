import Foundation.Constructions.Symmetric.PRFCounter

/-! Perfect ideal privacy from fresh counter inputs to a single random
function table. Resampling is an analysis identity, never a machine operation. -/
namespace Foundation.Symmetric.PRFCounter
open Foundation.Probability CryptoOracle
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem uniform_equiv {α : Type} [Fintype α] [Nonempty α] (e : α ≃ α) :
    (uniform α).map e = uniform α := by
  classical
  ext x
  rw [PMF.map_apply]
  have unique (a : α) : x = e a ↔ a = e.symm x := by
    constructor
    · intro h
      rw [h, e.symm_apply_apply]
    · intro h
      rw [h, e.apply_symm_apply]
  simp_rw [unique]
  simp [uniform]

private def maskEquiv {capacity length : Nat} (index : Fin capacity) (mask : Bits length) :
    (Fin capacity → Bits length) ≃ (Fin capacity → Bits length) where
  toFun table := Function.update table index (Bits.xor mask (table index))
  invFun table := Function.update table index (Bits.xor mask (table index))
  left_inv table := by
    funext j
    by_cases h : j = index
    · subst j; simp
    · simp [Function.update_of_ne h]
  right_inv table := by
    funext j
    by_cases h : j = index
    · subst j; simp
    · simp [Function.update_of_ne h]

/-- A single random-function entry can be independently refreshed without
changing the uniform table distribution. -/
theorem uniform_resample {capacity length : Nat} (index : Fin capacity) :
    (uniform (Fin capacity → Bits length)).bind (fun table =>
      (uniform (Bits length)).map (fun pad => Function.update table index pad)) =
    uniform (Fin capacity → Bits length) := by
  classical
  have htable (table : Fin capacity → Bits length) :
      (uniform (Bits length)).map (fun pad => Function.update table index pad) =
      (uniform (Bits length)).map (fun mask => maskEquiv index mask table) := by
    conv_lhs =>
      arg 2
      rw [← Bits.uniform_xor (table index)]
    rw [PMF.map_comp]
    congr 1
    funext mask
    simp only [Function.comp_def, maskEquiv, Equiv.coe_fn_mk, Bits.xor_comm]
  simp_rw [htable]
  change ((uniform (Fin capacity → Bits length)).bind fun table =>
    (uniform (Bits length)).bind fun mask => PMF.pure (maskEquiv index mask table)) = _
  rw [PMF.bind_comm]
  have hmask (mask : Bits length) :
      (uniform (Fin capacity → Bits length)).bind
        (fun table => PMF.pure (maskEquiv index mask table)) =
      uniform (Fin capacity → Bits length) := uniform_equiv (maskEquiv index mask)
  simp_rw [hmask]
  simp

/-- Once the counter advances, old entries cannot affect the output law. -/
theorem run_future_congr {capacity length : Nat} (left right : Fin capacity → Bits length)
    (choice : Bool) (counter : Nat) (attack : Attack length)
    (h : ∀ i, counter ≤ i.val → left i = right i) :
    (attack.run (oracle left choice) counter).map Outcome.result =
    (attack.run (oracle right choice) counter).map Outcome.result := by
  induction attack generalizing counter with
  | done result => simp [Program.run, PMF.pure_map]
  | query request next ih =>
      by_cases hc : counter < capacity
      · simp only [Program.run, oracle, hc, dite_true, PMF.pure_bind, PMF.map_comp,
          Function.comp_def]
        have he := h ⟨counter, hc⟩ (by rfl)
        simp only [encrypt, he]
        exact ih _ (counter + 1) (fun i hi => h i (by omega))
      · simp only [Program.run, oracle, hc, dite_false, PMF.pure_bind, PMF.map_comp,
          Function.comp_def]
        exact ih none counter h
  | coin next ih =>
      simp only [Program.run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit counter h


/-- Isolate a fresh coordinate while keeping all other table entries.
The continuation may depend on the sampled value, but may no longer inspect
this coordinate through its table argument. -/
theorem uniform_fresh {capacity length : Nat} {Result : Type}
    (index : Fin capacity)
    (f : Bits length → (Fin capacity → Bits length) → ProbComp Result)
    (h : ∀ table pad, f pad (Function.update table index pad) = f pad table) :
    (uniform (Fin capacity → Bits length)).bind (fun table => f (table index) table) =
    (uniform (Bits length)).bind (fun pad =>
      (uniform (Fin capacity → Bits length)).bind (f pad)) := by
  classical
  conv_lhs =>
    arg 1
    rw [← uniform_resample index]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, Function.update_self]
  simp_rw [h]
  exact PMF.bind_comm _ _ _

noncomputable def freshOracle (capacity length : Nat) :
    Oracle (Request length) (Response length) Nat :=
  fun counter _ => if counter < capacity then
    (uniform (Bits length)).map (fun ciphertext =>
      (counter + 1, some (counter, ciphertext)))
  else PMF.pure (counter, none)

private theorem uniform_xor_bind {length : Nat} {Result : Type} (message : Bits length)
    (f : Bits length → ProbComp Result) :
    (uniform (Bits length)).bind (fun pad => f (Bits.xor pad message)) =
      (uniform (Bits length)).bind f := by
  have h := congrArg (fun p : ProbComp (Bits length) => p.bind f) (Bits.uniform_xor message)
  simpa only [PMF.bind_map, Function.comp_def, Bits.xor_comm] using h

/-- A uniformly selected function queried at fresh counters is exactly the
experiment that samples an independent uniform ciphertext on each success.
The identity holds for arbitrary adaptive plaintext choices and local coins. -/
theorem ideal_fresh {capacity length : Nat} (attack : Attack length)
    (right : Bool) (counter : Nat) :
    (uniform (Fin capacity → Bits length)).bind (fun table =>
      (attack.run (oracle table right) counter).map Outcome.result) =
    (attack.run (freshOracle capacity length) counter).map Outcome.result := by
  classical
  induction attack generalizing counter with
  | done result => simp [Program.run, PMF.pure_map]
  | query request next ih =>
      by_cases hc : counter < capacity
      · simp only [Program.run, oracle, hc, dite_true, PMF.pure_bind, PMF.map_comp,
          Function.comp_def, encrypt]
        have hf := uniform_fresh (index := (⟨counter, hc⟩ : Fin capacity))
          (f := fun pad table =>
            ((next (some (counter, Bits.xor pad (selected right request)))).run
              (oracle table right) (counter + 1)).map Outcome.result)
          (h := by
            intro table pad
            apply run_future_congr
            intro i hi
            have hn : i ≠ (⟨counter, hc⟩ : Fin capacity) := by
              intro he
              have hv := congrArg Fin.val he
              simp only at hv
              omega
            simp [Function.update_of_ne hn])
        rw [hf]
        simp_rw [ih]
        rw [uniform_xor_bind (selected right request) (fun ciphertext =>
          ((next (some (counter, ciphertext))).run (freshOracle capacity length)
            (counter + 1)).map Outcome.result)]
        simp [freshOracle, hc, PMF.map_bind, PMF.bind_map, PMF.map_comp,
          Function.comp_def]
      · simp only [Program.run, oracle, hc, dite_false, PMF.pure_bind, PMF.map_comp,
          Function.comp_def]
        rw [ih]
        simp [freshOracle, hc, PMF.map_comp, Function.comp_def]
  | coin next ih =>
      simp only [Program.run, PMF.map_bind]
      rw [PMF.bind_comm]
      congr 1
      funext bit
      exact ih bit counter

/-- Exact ideal privacy includes counter exhaustion, zero capacity and
zero-length messages. No bound on the typed attack's query count is needed. -/
theorem ideal_privacy (S : Scheme) (n : Nat) (attack : Attack (S.length n)) :
    ideal S n false attack = ideal S n true attack := by
  let := S.toPRF.domainFinite n
  have hu : @uniform (S.toPRF.Domain n → Bits (S.toPRF.length n))
      (by classical exact inferInstance) inferInstance =
      uniform (Fin (S.capacity n) → Bits (S.length n)) := by
    have hi : (by classical exact inferInstance : Fintype
        (S.toPRF.Domain n → Bits (S.toPRF.length n))) =
        (inferInstance : Fintype (Fin (S.capacity n) → Bits (S.length n))) :=
      Subsingleton.elim _ _
    exact congrArg (fun i => @uniform (Fin (S.capacity n) → Bits (S.length n)) i inferInstance) hi
  unfold ideal runTable
  rw [hu]
  exact (ideal_fresh (capacity := S.capacity n) attack false 0).trans
    (ideal_fresh (capacity := S.capacity n) attack true 0).symm


/-- Perfect ideal privacy removes the middle term from the PRF reduction. -/
theorem advantage_le_prf (S : Scheme) (n : Nat) (attack : Attack (S.length n)) :
    probabilityGap (eventProb (real S n false attack) (· = true))
      (eventProb (real S n true attack) (· = true)) ≤
    (PRF.goal S.toPRF).advantage n () (reduce false 0 attack) +
      (PRF.goal S.toPRF).advantage n () (reduce true 0 attack) := by
  have h := advantage_bound S n attack
  rw [ideal_privacy S n attack] at h
  simpa [probabilityGap] using h

noncomputable def goal (S : Scheme) : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun n _ => Attack (S.length n)
  advantage := fun n _ attack => probabilityGap
    (eventProb (real S n false attack) (· = true))
    (eventProb (real S n true attack) (· = true))

def queryClass (S : Scheme) (q : Nat → Nat) : AdversaryClass (goal S) where
  admissible _ A := ∀ n, (A n).BoundedQueries (q n)

def QuerySecure (S : Scheme) (q : Nat → Nat) (ε : Nat → ℝ≥0∞) : Prop :=
  BoundedByOnWithin (goal S) (queryClass S q) (fun _ => ()) ε

/-- A common PRF bound for q queries yields twice that bound for adaptive
multiple encryption. This theorem restricts queries only, not CPU time. -/
theorem query_secure (S : Scheme) (q : Nat → Nat) (ε : Nat → ℝ≥0∞)
    (hPRF : PRF.QuerySecure S.toPRF q ε) : QuerySecure S q (fun n => 2 * ε n) := by
  intro A hA n
  have hl := hPRF (fun n => reduce false 0 (A n))
    (fun n => queries false 0 (A n) (q n) (hA n)) n
  have hr := hPRF (fun n => reduce true 0 (A n))
    (fun n => queries true 0 (A n) (q n) (hA n)) n
  exact (advantage_le_prf S n (A n)).trans (by simpa only [advantageProfile, two_mul] using add_le_add hl hr)


/-- The PRF assumption may give a different negligible profile to each
admitted attack family; a common epsilon is not required here. -/
theorem query_secure_asymptotic (S : Scheme) (q : Nat → Nat)
    (hPRF : SecureOnWithin (PRF.goal S.toPRF) (PRF.queryClass S.toPRF q) (fun _ => ())) :
    SecureOnWithin (goal S) (queryClass S q) (fun _ => ()) := by
  intro A hA
  have hl := hPRF (fun n => reduce false 0 (A n))
    (fun n => queries false 0 (A n) (q n) (hA n))
  have hr := hPRF (fun n => reduce true 0 (A n))
    (fun n => queries true 0 (A n) (q n) (hA n))
  apply Negligible.mono _ (Negligible.add hl hr)
  intro n
  exact advantage_le_prf S n (A n)

end Foundation.Symmetric.PRFCounter
