import Foundation.Machine.Adversary
import Foundation.Machine.PolynomialTime

universe u v w

namespace Machine

namespace MachineAdversaryInterface

/-- An eventual polynomial budget has a monomial bound at every input size
after absorbing its finite prefix into the coefficient. -/
theorem global_monomial_of_polynomiallyBounded
    {q : Nat → Nat} (hq : PolynomiallyBounded q) :
    ∃ c k : Nat, ∀ m, q m ≤ c * (m + 1) ^ k := by
  obtain ⟨c, k, he⟩ := hq
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  have hPrefix : ∀ N : Nat, ∃ C : Nat, ∀ m < N, q m ≤ C := by
    intro N
    induction N with
    | zero => exact ⟨0, by intro m hm; omega⟩
    | succ N ih =>
        obtain ⟨C, hC⟩ := ih
        refine ⟨max C (q N), ?_⟩
        intro m hm
        by_cases hlt : m < N
        · exact (hC m hlt).trans (le_max_left _ _)
        · have heq : m = N := by omega
          subst m
          exact le_max_right _ _
  obtain ⟨C, hC⟩ := hPrefix N
  refine ⟨max c C, k, ?_⟩
  intro m
  by_cases hm : m < N
  · calc
      q m ≤ C := hC m hm
      _ ≤ max c C := le_max_right _ _
      _ = max c C * 1 := by simp
      _ ≤ max c C * (m + 1) ^ k :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow' k m)
  · have hNm : N ≤ m := by omega
    exact (hN m hNm).trans
      (Nat.mul_le_mul_right _ (le_max_left c C))

/-- Machine-based polynomial-time adversaries relative to this finite-I/O
protocol adapter. One finite machine code and one valid runtime bound realize
the entire family. The input-size witness rules out hiding a superpolynomial
request or instance in the machine input. The adapter's `assemble` wiring is
an external protocol interpretation; its computational cost is not certified
by this class. -/
noncomputable def pptClass {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P) : AdversaryClass P where
  admissible F A :=
    ∃ (p : Program) (q : Nat → Nat) (size : J.InputSizeBound F),
      PolynomiallyBounded q ∧
      (∀ input : List Bool, HaltsWithin p input (q input.length)) ∧
      PolynomiallyBounded size.limit ∧
      J.Realizes F p q A

theorem pptClass_program_polynomialTime {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    {F : InstanceFamily P} {A : AdversaryFamily P F}
    (h : J.pptClass.admissible F A) :
    ∃ p : Program, PolynomialTime p := by
  obtain ⟨p, q, _, hq, hHalts, _, _⟩ := h
  exact ⟨p, q, hq, hHalts⟩

/-- The input-size witness is used to turn a machine bound in total input
length into a polynomial bound in the cryptographic security parameter for
every valid protocol request. -/
theorem pptClass_haltsWithin_securityPolynomial {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    {F : InstanceFamily P} {A : AdversaryFamily P F}
    (h : J.pptClass.admissible F A) :
    ∃ (p : Program) (b : Nat → Nat), PolynomiallyBounded b ∧
      ∀ n (request : J.Request n (F n)),
        HaltsWithin p (J.machineInput n (F n) request) (b n) := by
  obtain ⟨p, q, size, hq, hHalts, hSize, _⟩ := h
  obtain ⟨c, k, hGlobal⟩ := global_monomial_of_polynomiallyBounded hq
  let b : Nat → Nat := fun n => c * (size.limit n + 1) ^ k
  have hb : PolynomiallyBounded b := by
    exact (PolynomiallyBounded.const c).mul
      ((hSize.add (PolynomiallyBounded.const 1)).pow k)
  refine ⟨p, b, hb, ?_⟩
  intro n request
  let input := J.machineInput n (F n) request
  have hlen : input.length ≤ size.limit n := size.length_le n request
  have hqinput : q input.length ≤ b n := by
    calc
      q input.length ≤ c * (input.length + 1) ^ k := hGlobal _
      _ ≤ c * (size.limit n + 1) ^ k :=
        Nat.mul_le_mul_left c
          (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k)
  exact (hHalts input).mono hqinput

end MachineAdversaryInterface

end Machine
