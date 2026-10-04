import Foundation.Constructions.ElGamal.MachineNormalization

namespace ElGamal.Examples

/-- Deliberately arbitrary behavior on noncanonical bitstrings. Even an
arbitrary Lean function `policy` is permitted by the encoding round-trip law;
this example supplies no machine algorithm for evaluating that function. -/
def booleanDecoderPolicy (policy : List Bool → Option Bool) :
    Machine.FiniteBitEncoding Bool where
  encode bit := [bit]
  decode
    | [bit] => some bit
    | bits => policy bits
  decode_encode := by intro bit; rfl

example (policy : List Bool → Option Bool) (bit : Bool) :
    (booleanDecoderPolicy policy).decode ((booleanDecoderPolicy policy).encode bit) =
      some bit := rfl

example (policy : List Bool → Option Bool) (bit : Bool) :
    ((booleanDecoderPolicy policy).encode bit).length = 1 := rfl

example (policy other : List Bool → Option Bool) :
    (booleanDecoderPolicy policy).encode = (booleanDecoderPolicy other).encode := rfl

/-- Structurally well-delimited output whose first element field is empty.
Both encodings below agree on every encoded Boolean, yet the existing
choose adapter interprets this same raw output differently. -/
def noncanonicalChooseOutput (state : List Bool) : List Bool :=
  false :: (Machine.FiniteBitEncoding.delimit [] ++
    Machine.FiniteBitEncoding.delimit [false] ++ state)

example (state : List Bool) :
    interpretChooseResponse (booleanDecoderPolicy (fun _ => some true)) false
      (noncanonicalChooseOutput state) = (true, false, state) := by
  simp [interpretChooseResponse, responseCodeOfElement, noncanonicalChooseOutput,
    Machine.FiniteBitEncoding.sum, Machine.FiniteBitEncoding.prod,
    Machine.FiniteBitEncoding.bitstring, Machine.FiniteBitEncoding.delimit,
    Machine.FiniteBitEncoding.undelimit, booleanDecoderPolicy]

example (state : List Bool) :
    interpretChooseResponse (booleanDecoderPolicy (fun _ => none)) false
      (noncanonicalChooseOutput state) = (false, false, []) := by
  simp [interpretChooseResponse, responseCodeOfElement, noncanonicalChooseOutput,
    Machine.FiniteBitEncoding.sum, Machine.FiniteBitEncoding.prod,
    Machine.FiniteBitEncoding.bitstring, Machine.FiniteBitEncoding.delimit,
    Machine.FiniteBitEncoding.undelimit, booleanDecoderPolicy]

/-- For the represented arithmetic certificates too, changing a decoder
outside canonical encodings leaves all three fixed native programs and
budgets untouched. Valid-input arithmetic certificates do not constrain the
arbitrary-output validation performed by the IND-CPA adapter. -/
example
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {X : Nat → Type 1}
    {embed : ∀ n, X n → ConcreteInstance sampling n}
    (M : RepresentedMachinePrimitives sampling X embed)
    (decode : ∀ n (x : X n), List Bool → Option ((embed n x).params.Element))
    (hRoundTrip : ∀ n (x : X n) (a : (embed n x).params.Element),
      decode n x ((M.elementCode n x).encode a) = some a) :
    let M' := M.withElementDecoder decode hRoundTrip
    (M'.multiplyProgram, M'.powerProgram, M'.sampleProgram,
      M'.multiplyBudget, M'.powerBudget, M'.sampleBudget) =
    (M.multiplyProgram, M.powerProgram, M.sampleProgram,
      M.multiplyBudget, M.powerBudget, M.sampleBudget) := rfl

example
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {X : Nat → Type 1}
    {embed : ∀ n, X n → ConcreteInstance sampling n}
    {M : RepresentedMachinePrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M.toSimulatorPrimitives) : Machine.PolynomialTime N.program :=
  N.polynomialTime

/-- The local normalization certificate can be invoked as an ordinary
charged subroutine. This does not construct the surrounding ElGamal
simulator or prepare its tapes implicitly. -/
example
    {sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params)}
    {X : Nat → Type 1}
    {embed : ∀ n, X n → ConcreteInstance sampling n}
    {M : RepresentedMachinePrimitives sampling X embed}
    (N : RepresentedChooseNormalizer M.toSimulatorPrimitives)
    (pre suffix : Machine.Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ N.program.length → pre.length + pc ≠ returnPc)
    (n : Nat) (x : X n) (bits : List Bool) :
    let input := Machine.encodeSecurityParameter n ++
      Machine.frame ((M.instanceCode n).encode x) ++ Machine.frame bits
    (Machine.evalReturnWithin
      (Machine.Program.withSubroutine pre N.program suffix returnPc)
      returnPc ((Machine.Configuration.initial input).rebasePc pre.length)
      (N.budget input.length)).map
        (fun c => if c.pc = returnPc then some c.outputBits else none) =
      PMF.pure (some (normalizeChooseResponse (M.elementCode n x)
        (embed n x).params.generator bits)) := by
  dsimp only
  exact ((N.halts _).withSubroutine_evalReturn pre N.program suffix returnPc hLayout).trans
    (N.correct n x bits)

/-- Canonical re-encoding preserves exactly the chosen messages and state,
and its size is bounded independently of any machine implementation claim. -/
example {α : Type} (E : Machine.FiniteBitEncoding α) (defaultMessage : α)
    (bits : List Bool) :
    (responseCodeOfElement E).decode (normalizeChooseResponse E defaultMessage bits) =
      some (.inl (interpretChooseResponse E defaultMessage bits)) :=
  normalizeChooseResponse_decode _ _ _

end ElGamal.Examples
