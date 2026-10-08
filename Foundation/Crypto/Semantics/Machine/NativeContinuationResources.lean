import Foundation.Crypto.Semantics.Machine.NativeEncodedResources
import Foundation.Crypto.Semantics.Machine.NativeContinuation
import Foundation.Crypto.Semantics.Machine.ControlStorage

/-! Whole-prefix encoded storage for a producer followed by a native observer.
The complete retained producer state and its code can be included in E. The
observer code, physical tapes and control registers are then counted as well.
No termination or fixed native running time is required for these bounds. -/
namespace Machine.NativeContinuation.Resources
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (sourceStep : State → PMF State)
    (boundary : State → Bool) (publicMachine : State → Configuration) (code : Program)

/-- Every prefix is either still a producer prefix, or consists of a producer
prefix, exactly one transfer, and an actual native prefix. -/
def PrefixWitness (elapsed : Nat) (start : State) : Control State → Prop
  | .producing state => state ∈ (eval sourceStep elapsed start).support
  | .observing saved machine => ∃ before after,
      before + 1 + after = elapsed ∧
      saved ∈ (eval sourceStep before start).support ∧ boundary saved = true ∧
      machine ∈ (eval (stepPMF code) after ((publicMachine saved).resumeAt 0)).support

theorem prefix_witness (elapsed : Nat) (start : State) (target : Control State)
    (h : target ∈ (eval (step sourceStep boundary publicMachine code) elapsed (.producing start)).support) :
    PrefixWitness sourceStep boundary publicMachine code elapsed start target := by
  induction elapsed generalizing start target with
  | zero =>
      rw [eval, PMF.mem_support_pure_iff] at h
      subst target
      simp [PrefixWitness, eval]
  | succ elapsed ih =>
      rw [eval, PMF.mem_support_bind_iff] at h
      obtain ⟨next, hn, ht⟩ := h
      by_cases hb : boundary start = true
      · simp only [step, hb, ↓reduceIte, PMF.mem_support_pure_iff] at hn
        subst next
        rw [observing_eval, PMF.mem_support_map_iff] at ht
        obtain ⟨machine, hm, rfl⟩ := ht
        exact ⟨0, elapsed, by omega, by simp [eval], hb, hm⟩
      · simp only [step, hb, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at hn
        obtain ⟨next, hn, rfl⟩ := hn
        have hw := ih next target ht
        cases target with
        | producing state =>
            change state ∈ (eval sourceStep (elapsed + 1) start).support
            rw [eval, PMF.mem_support_bind_iff]
            exact ⟨next, hn, hw⟩
        | observing saved machine =>
            obtain ⟨before, after, hTime, hs, hb, hm⟩ := hw
            refine ⟨before + 1, after, by omega, ?_, hb, hm⟩
            rw [eval, PMF.mem_support_bind_iff]
            exact ⟨next, hn, hs⟩

def encoding (E : FiniteBitEncoding State) : FiniteBitEncoding (Control State) :=
  (E.sum (E.prod ConfigurationEncoding.configuration)).retract
    (fun target => match target with
      | .producing state => .inl state
      | .observing saved machine => .inr (saved, machine))
    (fun fields => match fields with
      | .inl state => .producing state
      | .inr (saved, machine) => .observing saved machine)
    (fun target => by cases target <;> rfl)

def programEncoding : FiniteBitEncoding Program :=
  Program.bitEncoding

def completeEncoding (E : FiniteBitEncoding State) :=
  programEncoding.prod (encoding E)

def bound (code : Program) (sourceCap publicTapeCap horizon : Nat) : Nat :=
  2 * (Program.encode code).length + 2 * sourceCap +
    2 * (horizon * (code.addressCap + 1)) + 18 * (publicTapeCap + horizon) + 17

theorem bound_mono {firstSource nextSource firstPublic nextPublic : Nat}
    (hSource : firstSource ≤ nextSource) (hPublic : firstPublic ≤ nextPublic) (horizon : Nat) :
    bound code firstSource firstPublic horizon ≤ bound code nextSource nextPublic horizon := by
  unfold bound
  omega

variable (E : FiniteBitEncoding State) (start : State) (sourceCap publicTapeCap horizon : Nat)
    (hSource : ∀ elapsed ≤ horizon, ∀ state ∈ (eval sourceStep elapsed start).support,
      (E.encode state).length ≤ sourceCap)
    (hPublic : ∀ elapsed ≤ horizon, ∀ state ∈ (eval sourceStep elapsed start).support,
      boundary state = true → (publicMachine state).tapeCells ≤ publicTapeCap)

include hSource hPublic in
/-- Counts the observer code plus the full saved producer encoding on every
supported branch and every prefix up to the requested horizon. -/
theorem encoded_peak (elapsed : Nat) (hElapsed : elapsed ≤ horizon) (target : Control State)
    (h : target ∈ (eval (step sourceStep boundary publicMachine code) elapsed (.producing start)).support) :
    ((completeEncoding E).encode (code, target)).length ≤ bound code sourceCap publicTapeCap horizon := by
  have hw := prefix_witness sourceStep boundary publicMachine code elapsed start target h
  cases target with
  | producing state =>
      have hs := hSource elapsed hElapsed state hw
      simp only [completeEncoding, encoding, FiniteBitEncoding.prod_encode_length,
        programEncoding, Program.bitEncoding, FiniteBitEncoding.retract_encode_length,
        FiniteBitEncoding.sum_encode_inl_length]
      unfold bound
      omega
  | observing saved machine =>
      obtain ⟨before, after, hTime, hs, hb, hm⟩ := hw
      have hBefore : before ≤ horizon := by omega
      have hAfter : after ≤ horizon := by omega
      have hSaved := hSource before hBefore saved hs
      have hPublicCells := hPublic before hBefore saved hs hb
      have hp := pc_prefix code horizon after hAfter ((publicMachine saved).resumeAt 0) machine hm
      have ht := tapeCells_prefix code horizon after hAfter ((publicMachine saved).resumeAt 0) machine hm
      have he := ConfigurationEncoding.configuration_length_le machine
      simp only [Configuration.resumeAt, Configuration.tapeCells] at hp ht
      change machine.tapeCells ≤ (publicMachine saved).tapeCells + horizon at ht
      simp only [completeEncoding, encoding, FiniteBitEncoding.prod_encode_length,
        programEncoding, Program.bitEncoding, FiniteBitEncoding.retract_encode_length,
        FiniteBitEncoding.sum_encode_inr_length]
      unfold bound
      omega

/-- Fixed observer code preserves polynomial encoded-storage profiles. -/
theorem bound_polynomial {sourceCap publicTapeCap horizon : Nat → Nat}
    (hSource : PolynomiallyBounded sourceCap) (hPublic : PolynomiallyBounded publicTapeCap)
    (hTime : PolynomiallyBounded horizon) :
    PolynomiallyBounded (fun n => bound code (sourceCap n) (publicTapeCap n) (horizon n)) :=
  (((((PolynomiallyBounded.const (2 * (Program.encode code).length)).add
    ((PolynomiallyBounded.const 2).mul hSource)).add
      ((PolynomiallyBounded.const 2).mul
        (hTime.mul (PolynomiallyBounded.const (code.addressCap + 1))))).add
          ((PolynomiallyBounded.const 18).mul (hPublic.add hTime))).add
            (PolynomiallyBounded.const 17))

end Machine.NativeContinuation.Resources
