import Foundation.Machine.Execution
import Foundation.Asymptotics.PolynomiallyBounded

namespace Machine

/-- A fixed finite machine program halts on every random branch within a
polynomial bound in the *total input bit length*. The quantified program is
outside the input quantifier. This is a worst-case step-count property, not an
expected-time bound. Cryptographic applications additionally need a bound on
the encoded protocol input length as a function of the security parameter. -/
def PolynomialTime (p : Program) : Prop :=
  ∃ q : Nat → Nat,
    PolynomiallyBounded q ∧
    ∀ input : List Bool, HaltsWithin p input (q input.length)

end Machine
