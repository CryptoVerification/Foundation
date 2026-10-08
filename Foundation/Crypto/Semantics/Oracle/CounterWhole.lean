import Foundation.Crypto.Semantics.Oracle.CounterMasking
import Foundation.Crypto.Semantics.Asymptotic.PolynomiallyBounded

/-! Whole-execution simulation. The source machine's encryption oracle is
one challenger capability; the target implements it with the finite cell
controller. Safety certifies the source execution, never assumes target
termination or distributional correctness. -/
namespace CryptoOracle.CounterMasking.Whole
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

-- These functions describe challenger state, not target CPU instructions.
def selectList (side : Bool) : List Bool → List Bool
  | left :: right :: rest => (if side then right else left) :: selectList side rest
  | _ => []

theorem selectList_interleave (side : Bool) (left right : List Bool)
    (h : left.length = right.length) :
    selectList side (interleave left right) = if side then right else left := by
  induction left generalizing right with
  | nil =>
      have hr : right = [] := List.length_eq_zero_iff.mp h.symm
      subst right
      cases side <;> rfl
  | cons bit rest ih =>
      cases right with
      | nil => simp at h
      | cons r rs =>
          simp only [interleave, selectList, ih rs (by simpa using h)]
          cases side <;> rfl

def fail (c : Configuration) (machine : Machine.Configuration) (request : List Bool) : Configuration :=
  { c with phase := .source, source := { c.source with control := .loading machine [false] {}, reverseTrace := (request, [false]) :: c.source.reverseTrace } }

def succeed (c : Configuration) (rest : List Bool) (machine : Machine.Configuration)
    (request mask pad : List Bool) : Configuration :=
  let encoded := c.counter.reverse ++ [false]
  let reply := true :: (c.counter.reverse ++ false :: xorList mask pad)
  { c with capacity := rest, phase := .source, counter := true :: c.counter, source := { c.source with control := .loading machine reply {}, reverseTrace := (request, reply) :: c.source.reverseTrace }, reverseTrace := (encoded, pad) :: c.reverseTrace }

/-- A source encryption oracle has unit capability cost. Its ghost PRF
trace is retained to compare it with actual target queries. -/
noncomputable def sourceStep (code : Code) (pad : List Bool → List Bool)
    (c : Configuration) : ProbComp Configuration :=
  match Interactive.transition code.program c.source with
  | .deterministic next => PMF.pure { c with source := next }
  | .random zero one => sampleBit.map (fun bit => { c with source := if bit then one else zero })
  | .oracleCall machine request =>
      match c.capacity with
      | [] => PMF.pure (fail c machine request)
      | _ :: rest => PMF.pure (succeed c rest machine request
          (selectList code.side request) (pad (c.counter.reverse ++ [false])))

noncomputable def sourceRun (code : Code) (pad : List Bool → List Bool) :
    Nat → Configuration → ProbComp Configuration
  | 0, c => PMF.pure c
  | fuel + 1, c => (sourceStep code pad c).bind (sourceRun code pad fuel)

/-- Reached source calls have paired plaintexts of the declared length.
The target proof also checks each pad's length, including all future calls. -/
def WellFormed (_code : Code) (pad : List Bool → List Bool) (length : Nat)
    (c : Configuration) : Prop :=
  c.phase = .source ∧
  ∀ machine request, c.source.control = .awaiting machine request → c.capacity ≠ [] →
    ∃ left right, request = interleave left right ∧ left.length = length ∧
      right.length = length ∧ (pad (c.counter.reverse ++ [false])).length = length

/-- A finite source execution certificate over every supported local coin.
At fuel zero it requires genuine completion; positive fuel checks the
current request layout and recursively certifies source successors. -/
def Safe (code : Code) (pad : List Bool → List Bool) (length : Nat) :
    Nat → Configuration → Prop
  | 0, c => complete c
  | fuel + 1, c => WellFormed code pad length c ∧
      ∀ next ∈ (sourceStep code pad c).support, Safe code pad length fuel next

noncomputable def bitOracle (pad : List Bool → List Bool) : Interactive.BitOracle Unit :=
  fun _ request => PMF.pure ((), pad request)

theorem sourceRun_complete (code : Code) (pad : List Bool → List Bool) (length fuel : Nat)
    (c : Configuration) (h : Safe code pad length fuel c) :
    ∀ out ∈ (sourceRun code pad fuel c).support, complete out := by
  induction fuel generalizing c with
  | zero =>
      intro out ho
      simp only [sourceRun, PMF.mem_support_pure_iff] at ho
      subst out
      exact h
  | succ fuel ih =>
      intro out ho
      rw [sourceRun, PMF.mem_support_bind_iff] at ho
      obtain ⟨next, hn, ho⟩ := ho
      exact ih next (h.2 next hn) out ho

theorem sourceStep_counter (code : Code) (pad : List Bool → List Bool) (c : Configuration)
    (next : Configuration) (h : next ∈ (sourceStep code pad c).support) :
    next.counter.length ≤ c.counter.length + 1 := by
  cases ht : Interactive.transition code.program c.source with
  | deterministic saved =>
      simp only [sourceStep, ht, PMF.mem_support_pure_iff] at h
      subst next
      simp
  | random zero one =>
      simp only [sourceStep, ht, PMF.mem_support_map_iff] at h
      obtain ⟨coin, _, he⟩ := h
      subst next
      simp
  | oracleCall machine request =>
      cases hc : c.capacity with
      | nil =>
          simp only [sourceStep, ht, hc, PMF.mem_support_pure_iff] at h
          subst next
          simp [fail]
      | cons token rest =>
          simp only [sourceStep, ht, hc, PMF.mem_support_pure_iff] at h
          subst next
          simp [succeed]

/-- A source transition is implemented by a target segment. The length of
the segment may depend on public tape data, while the code remains fixed. -/
theorem segment (code : Code) (pad : List Bool → List Bool) (length : Nat)
    (c : Configuration) (h : WellFormed code pad length c) :
    ∃ used, 1 ≤ used ∧ used ≤ 4 * length + 2 * c.counter.length + 9 ∧
      eval code (bitOracle pad) c used = sourceStep code pad c := by
  obtain ⟨phase, valid⟩ := h
  cases ht : Interactive.transition code.program c.source with
  | deterministic next =>
      refine ⟨1, by omega, by omega, ?_⟩
      simp [eval, step, transition, phase, sourceStep, ht]
  | random zero one =>
      refine ⟨1, by omega, by omega, ?_⟩
      simp only [eval, PMF.pure_bind, step, transition, phase, ht, sourceStep]
      congr 1
      funext coin
      cases coin <;> rfl
  | oracleCall machine request =>
      have control : c.source.control = .awaiting machine request := by
        cases hc : c.source.control <;> simp [Interactive.transition, hc] at ht
        case awaiting saved bits => simp_all
        all_goals (repeat' split at ht) <;> simp_all
      cases cap : c.capacity with
      | nil =>
          refine ⟨2, by omega, by omega, ?_⟩
          rw [query_exhausted_eval code (bitOracle pad) c machine request phase cap control]
          simp [sourceStep, ht, cap, fail]
      | cons token rest =>
          obtain ⟨left, right, hr, hl, hright, hp⟩ := valid machine request control (by simp [cap])
          subst request
          have eqLen : left.length = right.length := hl.trans hright.symm
          refine ⟨4 * left.length + 2 * c.counter.length + 9, by omega, by omega, ?_⟩
          rw [query_success_eval code (bitOracle pad) c machine token rest left right
            (pad (c.counter.reverse ++ [false])) eqLen (hp.trans hl.symm) phase cap control rfl]
          simp [sourceStep, ht, cap, succeed, selectList_interleave code.side left right eqLen]



/-- Ordinary source stopping and layout facts suffice to construct safety.
No controller or target-execution fact appears among these premises. -/
theorem safe_of_source (code : Code) (pad : List Bool → List Bool) (length fuel : Nat)
    (c : Configuration)
    (halts : ∀ out ∈ (sourceRun code pad fuel c).support, complete out)
    (layout : ∀ elapsed < fuel, ∀ out ∈ (sourceRun code pad elapsed c).support,
      WellFormed code pad length out) : Safe code pad length fuel c := by
  induction fuel generalizing c with
  | zero =>
      apply halts c
      simp [sourceRun]
  | succ fuel ih =>
      refine ⟨layout 0 (by omega) c (by simp [sourceRun]), ?_⟩
      intro next hn
      apply ih next
      · intro out ho
        apply halts out
        rw [sourceRun, PMF.mem_support_bind_iff]
        exact ⟨next, hn, ho⟩
      · intro elapsed he out ho
        apply layout (elapsed + 1) (by omega) out
        rw [sourceRun, PMF.mem_support_bind_iff]
        exact ⟨next, hn, ho⟩

private theorem transition_trace (program : Interactive.Code) (c : Interactive.Configuration Unit) :
    match Interactive.transition program c with
    | .deterministic next => next.reverseTrace = c.reverseTrace
    | .random zero one => zero.reverseTrace = c.reverseTrace ∧ one.reverseTrace = c.reverseTrace
    | .oracleCall _ _ => True := by
  cases hc : c.control <;> simp only [Interactive.transition, hc]
  all_goals (repeat' split at *)
  all_goals try simp_all
  all_goals subst_vars
  all_goals try rfl
  all_goals
    obtain ⟨hz, ho⟩ := (show _ ∧ _ from by assumption)
    subst_vars
    exact ⟨rfl, rfl⟩

/-- A PRF call occurs only on a successful encryption call. Rejected calls
are retained in the source transcript but cannot add target queries. -/
theorem sourceStep_trace (code : Code) (pad : List Bool → List Bool) (c next : Configuration)
    (h : c.reverseTrace.length ≤ c.source.reverseTrace.length)
    (hn : next ∈ (sourceStep code pad c).support) :
    next.reverseTrace.length ≤ next.source.reverseTrace.length := by
  have ht := transition_trace code.program c.source
  cases tr : Interactive.transition code.program c.source with
  | deterministic saved =>
      simp only [tr] at ht
      simp only [sourceStep, tr, PMF.mem_support_pure_iff] at hn
      subst next
      simpa [ht] using h
  | random zero one =>
      simp only [tr] at ht
      simp only [sourceStep, tr, PMF.mem_support_map_iff] at hn
      obtain ⟨coin, _, he⟩ := hn
      subst next
      cases coin <;> simpa [ht] using h
  | oracleCall machine request =>
      cases cap : c.capacity with
      | nil =>
          simp only [sourceStep, tr, cap, PMF.mem_support_pure_iff] at hn
          subst next
          simp only [fail, List.length_cons]
          omega
      | cons token rest =>
          simp only [sourceStep, tr, cap, PMF.mem_support_pure_iff] at hn
          subst next
          simp only [succeed, List.length_cons]
          omega

theorem sourceRun_trace (code : Code) (pad : List Bool → List Bool) (fuel : Nat)
    (c : Configuration) (h : c.reverseTrace.length ≤ c.source.reverseTrace.length)
    (out : Configuration) (ho : out ∈ (sourceRun code pad fuel c).support) :
    out.reverseTrace.length ≤ out.source.reverseTrace.length := by
  induction fuel generalizing c with
  | zero =>
      simp only [sourceRun, PMF.mem_support_pure_iff] at ho
      subst out
      exact h
  | succ fuel ih =>
      rw [sourceRun, PMF.mem_support_bind_iff] at ho
      obtain ⟨next, hn, ho⟩ := ho
      exact ih next (sourceStep_trace code pad c next h hn) ho
/-- Uniform whole-runtime bound; multiplication is a conservative bound
that avoids rebuilding or padding the executable code for each parameter. -/
def budget (length sourceTime : Nat) : Nat := sourceTime * (4 * length + 2 * sourceTime + 9)


/-- Exact whole-distribution simulation with a uniform conservative budget.
Completion allows different physical segment lengths on different branches
without changing the final distribution by padding. -/
theorem run (code : Code) (pad : List Bool → List Bool) (length maxCounter fuel : Nat)
    (c : Configuration) (safe : Safe code pad length fuel c)
    (counter : c.counter.length + fuel ≤ maxCounter) :
    eval code (bitOracle pad) c (fuel * (4 * length + 2 * maxCounter + 9)) =
      sourceRun code pad fuel c := by
  induction fuel generalizing c with
  | zero => simp [eval, sourceRun]
  | succ fuel ih =>
      obtain ⟨used, hpos, hused, segmentEq⟩ := segment code pad length c safe.1
      let delay := 4 * length + 2 * maxCounter + 9
      have hd : used ≤ delay := by dsimp [delay]; omega
      have ht : (fuel + 1) * (4 * length + 2 * maxCounter + 9) =
          used + (fuel * (4 * length + 2 * maxCounter + 9) + (delay - used)) := by
        rw [Nat.add_mul, Nat.one_mul]
        dsimp [delay] at *
        omega
      rw [ht, eval_add, segmentEq, ← PMF.bindOnSupport_eq_bind]
      conv_rhs => rw [sourceRun, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext next hn
      have hc := sourceStep_counter code pad c next hn
      have hsafe := safe.2 next hn
      have heq := ih next hsafe (by omega)
      have halt : HaltsWithin code (bitOracle pad) next
          (fuel * (4 * length + 2 * maxCounter + 9)) := by
        intro out ho
        rw [heq] at ho
        exact sourceRun_complete code pad length fuel next hsafe out ho
      rw [eval_stable code (bitOracle pad) next _ _ halt, heq]

/-- No target stopping premise is needed: source safety proves target
termination, with precisely the same compiled finite code. -/
theorem halts (code : Code) (pad : List Bool → List Bool) (length fuel : Nat)
    (input capacity : List Bool)
    (safe : Safe code pad length fuel (initial input capacity)) :
    HaltsWithin code (bitOracle pad) (initial input capacity) (budget length fuel) := by
  intro out ho
  rw [budget, run code pad length fuel fuel (initial input capacity) safe (by simp [initial])] at ho
  exact sourceRun_complete code pad length fuel (initial input capacity) safe out ho

/-- Every observation or resource derived from the final configuration is
preserved, including state and the actual PRF transcript. -/
theorem run_map (code : Code) (pad : List Bool → List Bool) (length fuel : Nat)
    (input capacity : List Bool) (safe : Safe code pad length fuel (initial input capacity))
    {Result : Type} (observe : Configuration → Result) :
    (eval code (bitOracle pad) (initial input capacity) (budget length fuel)).map observe =
      (sourceRun code pad fuel (initial input capacity)).map observe := by
  rw [budget, run code pad length fuel fuel (initial input capacity) safe (by simp [initial])]

theorem budget_polynomial {length time : Nat → Nat}
    (hl : PolynomiallyBounded length) (ht : PolynomiallyBounded time) :
    PolynomiallyBounded (fun n => budget (length n) (time n)) :=
  ht.mul ((((PolynomiallyBounded.const 4).mul hl).add
    ((PolynomiallyBounded.const 2).mul ht)).add (PolynomiallyBounded.const 9))


/-- The original encryption-query bound bounds the target's actual PRF
calls. The comparison uses the full final distribution proved above. -/
theorem queries (code : Code) (pad : List Bool → List Bool) (length fuel queryBound : Nat)
    (input capacity : List Bool) (safe : Safe code pad length fuel (initial input capacity))
    (sourceQueries : ∀ out ∈ (sourceRun code pad fuel (initial input capacity)).support,
      out.source.reverseTrace.length ≤ queryBound) :
    ∀ out ∈ (eval code (bitOracle pad) (initial input capacity) (budget length fuel)).support,
      out.reverseTrace.length ≤ queryBound := by
  intro out ho
  rw [budget, run code pad length fuel fuel (initial input capacity) safe (by simp [initial])] at ho
  exact (sourceRun_trace code pad fuel (initial input capacity)
    (by simp [initial, Interactive.Configuration.initial]) out ho).trans (sourceQueries out ho)

end CryptoOracle.CounterMasking.Whole
