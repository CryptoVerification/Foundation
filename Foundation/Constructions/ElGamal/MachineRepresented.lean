import Foundation.Constructions.ElGamal.ConcreteReduction
import Foundation.Machine.CryptoInterfaces
import Foundation.Machine.INDCPAReachability
import Foundation.Machine.Security

namespace ElGamal

open Foundation.Probability

/-- Stage requests of the represented ElGamal game, using only the finite
group-element code and the identity bitstring code. -/
def requestCodeOfElement {α : Type}
    (E : Machine.FiniteBitEncoding α) :
    Machine.FiniteBitEncoding (α ⊕ (List Bool × (α × α))) :=
  E.sum (Machine.FiniteBitEncoding.bitstring.prod (E.prod E))

theorem requestCodeOfElement_choose_length {α : Type}
    (E : Machine.FiniteBitEncoding α) (key : α) :
    ((requestCodeOfElement E).encode (.inl key)).length =
      (E.encode key).length + 1 := by
  rfl

theorem requestCodeOfElement_guess_length {α : Type}
    (E : Machine.FiniteBitEncoding α)
    (state : List Bool) (c₁ c₂ : α) :
    ((requestCodeOfElement E).encode (.inr (state, (c₁, c₂)))).length =
      2 * state.length + 2 * (E.encode c₁).length +
        (E.encode c₂).length + 3 := by
  simp [requestCodeOfElement, Machine.FiniteBitEncoding.bitstring]
  omega

/-- Stage responses keep the adversary state as the final raw bitstring.
Its decoder therefore cannot inflate the state hidden in a short code. -/
def responseCodeOfElement {α : Type}
    (E : Machine.FiniteBitEncoding α) :
    Machine.FiniteBitEncoding ((α × α × List Bool) ⊕ Bool) :=
  (E.prod (E.prod Machine.FiniteBitEncoding.bitstring)).sum
    Machine.FiniteBitEncoding.bool

theorem responseCodeOfElement_state_length_le {α : Type}
    (E : Machine.FiniteBitEncoding α)
    (bits : List Bool) (m₀ m₁ : α) (state : List Bool)
    (h : (responseCodeOfElement E).decode bits =
      some (.inl (m₀, m₁, state))) :
    state.length ≤ bits.length := by
  have hBit : ∀ code value,
      Machine.FiniteBitEncoding.bitstring.decode code = some value →
        value.length ≤ code.length := by
    intro code value hDecode
    simp [Machine.FiniteBitEncoding.bitstring] at hDecode
    subst value
    rfl
  have hPair : ∀ code (pair : α × List Bool),
      ((E.prod Machine.FiniteBitEncoding.bitstring).decode code = some pair) →
        pair.2.length ≤ code.length := by
    intro code pair hDecode
    rcases pair with ⟨value, rest⟩
    exact Machine.FiniteBitEncoding.prod_decode_right_size_le
      E Machine.FiniteBitEncoding.bitstring List.length hBit
      code value rest hDecode
  cases bits with
  | nil => simp [responseCodeOfElement, Machine.FiniteBitEncoding.sum] at h
  | cons tag rest =>
      cases tag with
      | false =>
          have hTriple :
              (E.prod (E.prod Machine.FiniteBitEncoding.bitstring)).decode rest =
                some (m₀, m₁, state) := by
            simpa [responseCodeOfElement, Machine.FiniteBitEncoding.sum] using h
          have hle := Machine.FiniteBitEncoding.prod_decode_right_size_le
            E (E.prod Machine.FiniteBitEncoding.bitstring)
            (fun pair => pair.2.length) hPair rest m₀ (m₁, state) hTriple
          exact hle.trans (by simp)
      | true =>
          simp [responseCodeOfElement, Machine.FiniteBitEncoding.sum] at h

theorem responseCodeOfElement_chooseStateSizeFaithful
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (elementCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding ((embed n x).params.Element)) :
    Machine.ChooseStateSizeFaithful X
      (fun n x => (embed n x).toElGamalInstance.scheme)
      (fun n x => responseCodeOfElement (elementCode n x)) := by
  intro n x bits m₀ m₁ state h
  exact responseCodeOfElement_state_length_le (elementCode n x)
    bits m₀ m₁ state h

/-- ElGamal instances selected through a representation `X`. A finite code
for `X n` can be supplied without claiming that the entire mathematical
`ConcreteInstance` type has a finite code. -/
noncomputable def representedINDCPAGoal
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n) : CryptoGoal :=
  (INDCPA ProbComp concreteINDCPASemantics).reindex X
    (fun n x => (embed n x).toElGamalInstance.scheme)

/-- DDH on the same representation, observing the parameters embedded in
each represented concrete ElGamal instance. -/
noncomputable def representedDDHGoal
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n) : CryptoGoal :=
  (DDH ProbComp (concreteDDHSemantics sampling)).reindex X
    (fun n x => (embed n x).params)

/-- The Phase 11 concrete advantage equality, restricted to the represented
instances. The reduction changes the adversary but keeps the finite instance
descriptor `x`; no new probability argument is required. -/
noncomputable def representedReduction
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n) :
    Reduction (representedINDCPAGoal sampling X embed)
      (representedDDHGoal sampling X embed) where
  mapInstance := fun x => x
  reduce := fun x A =>
    ddhAdversaryOfINDCPA sampleBit (embed _ x).toElGamalInstance A
  loss := AdvantageBound.id
  advantage_le := by
    intro n x A
    exact le_of_eq (concreteCompatibility_eq sampling n (embed n x) A)

/-- Finite input/output protocol for the represented IND-CPA goal. The
stage-specific encodings are stated at each represented instance, avoiding
an encoding assumption for all mathematical PKE objects. -/
noncomputable def representedINDCPAInterface
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (instanceCode : ∀ n, Machine.FiniteBitEncoding (X n))
    (requestCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding
        ((embed n x).toElGamalInstance.scheme.PublicKey ⊕
          (List Bool × (embed n x).toElGamalInstance.scheme.Ciphertext)))
    (responseCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding
        (((embed n x).toElGamalInstance.scheme.Message ×
          (embed n x).toElGamalInstance.scheme.Message × List Bool) ⊕ Bool))
    (defaultMessage : ∀ n (x : X n),
      (embed n x).toElGamalInstance.scheme.Message) :
    Machine.MachineAdversaryInterface
      (representedINDCPAGoal sampling X embed) :=
  Machine.indCPAReindexedInterface concreteINDCPASemantics X
    (fun n x => (embed n x).toElGamalInstance.scheme)
    instanceCode requestCode responseCode defaultMessage

/-- A concrete protocol adapter built from one code for each represented
instance and one code for its group elements. `generator` is used only as
the fallback message if machine output is invalid. -/
noncomputable def representedINDCPAElementInterface
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (instanceCode : ∀ n, Machine.FiniteBitEncoding (X n))
    (elementCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding ((embed n x).params.Element)) :
    Machine.MachineAdversaryInterface
      (representedINDCPAGoal sampling X embed) :=
  representedINDCPAInterface sampling X embed instanceCode
    (fun n x => requestCodeOfElement (elementCode n x))
    (fun n x => responseCodeOfElement (elementCode n x))
    (fun n x => (embed n x).params.generator)

/-- The represented ElGamal IND-CPA protocol can use the reachable-request
machine class. Construction requires a size-faithful choose-response decoder;
membership further requires polynomial size laws for the chosen input codes
and a single worst-case polynomial-time machine code.
It does not assert that an ElGamal simulator compiler has been built. -/
noncomputable def representedINDCPAReachablePPTClass
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (instanceCode : ∀ n, Machine.FiniteBitEncoding (X n))
    (requestCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding
        ((embed n x).toElGamalInstance.scheme.PublicKey ⊕
          (List Bool × (embed n x).toElGamalInstance.scheme.Ciphertext)))
    (responseCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding
        (((embed n x).toElGamalInstance.scheme.Message ×
          (embed n x).toElGamalInstance.scheme.Message × List Bool) ⊕ Bool))
    (defaultMessage : ∀ n (x : X n),
      (embed n x).toElGamalInstance.scheme.Message)
    (hFaithful : Machine.ChooseStateSizeFaithful X
      (fun n x => (embed n x).toElGamalInstance.scheme) responseCode) :
    AdversaryClass (representedINDCPAGoal sampling X embed) :=
  Machine.indCPAReindexedReachablePPTClass concreteINDCPASemantics X
    (fun n x => (embed n x).toElGamalInstance.scheme)
    instanceCode requestCode responseCode defaultMessage hFaithful

/-- The reachable-request class for the concrete element-based adapter.
The required state-size fidelity follows from its explicit response code. -/
noncomputable def representedINDCPAElementPPTClass
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (instanceCode : ∀ n, Machine.FiniteBitEncoding (X n))
    (elementCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding ((embed n x).params.Element)) :
    AdversaryClass (representedINDCPAGoal sampling X embed) :=
  representedINDCPAReachablePPTClass sampling X embed instanceCode
    (fun n x => requestCodeOfElement (elementCode n x))
    (fun n x => responseCodeOfElement (elementCode n x))
    (fun n x => (embed n x).params.generator)
    (responseCodeOfElement_chooseStateSizeFaithful sampling X embed elementCode)

/-- The element-based two-stage adapter has polynomial request sizes on
choose and a linear dependence on the state length on guess. This is the
explicit size discipline used by the reachable-request class. -/
theorem representedINDCPAElement_inputSizeLaws
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (instanceCode : ∀ n, Machine.FiniteBitEncoding (X n))
    (elementCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding ((embed n x).params.Element))
    (instanceSize elementSize : Nat → Nat)
    (hInstance : ∀ n (x : X n),
      ((instanceCode n).encode x).length ≤ instanceSize n)
    (hElement : ∀ n (x : X n) (e : (embed n x).params.Element),
      ((elementCode n x).encode e).length ≤ elementSize n)
    (hInstancePoly : PolynomiallyBounded instanceSize)
    (hElementPoly : PolynomiallyBounded elementSize)
    (F : (n : Nat) → X n) :
    ∃ size : Nat → Nat, PolynomiallyBounded size ∧
      (∀ n (pk : (embed n (F n)).params.Element),
        ((representedINDCPAElementInterface sampling X embed instanceCode
          elementCode).machineInput n (F n) (.inl pk)).length ≤ size n) ∧
      (∀ n (state : List Bool)
        (ciphertext : (embed n (F n)).params.Element ×
          (embed n (F n)).params.Element),
        ((representedINDCPAElementInterface sampling X embed instanceCode
          elementCode).machineInput n (F n)
            (.inr (state, ciphertext))).length ≤
          size n * (state.length + 1)) := by
  let size : Nat → Nat := fun n =>
    n + 13 + 2 * instanceSize n + 6 * elementSize n
  have hSizePoly : PolynomiallyBounded size := by
    exact (((PolynomiallyBounded.id.add (PolynomiallyBounded.const 13)).add
      ((PolynomiallyBounded.const 2).mul hInstancePoly)).add
        ((PolynomiallyBounded.const 6).mul hElementPoly))
  refine ⟨size, hSizePoly, ?_, ?_⟩
  · intro n pk
    let J := representedINDCPAElementInterface sampling X embed
      instanceCode elementCode
    have hLen := J.machineInput_length n (F n) (.inl pk)
    have hi := hInstance n (F n)
    have he := hElement n (F n) pk
    change (J.machineInput n (F n) (.inl pk)).length =
      n + 3 + 2 * ((instanceCode n).encode (F n)).length +
        2 * ((requestCodeOfElement (elementCode n (F n))).encode
          (.inl pk)).length at hLen
    rw [requestCodeOfElement_choose_length] at hLen
    change (J.machineInput n (F n) (.inl pk)).length ≤ size n
    dsimp [size]
    omega
  · intro n state ciphertext
    rcases ciphertext with ⟨c₁, c₂⟩
    let J := representedINDCPAElementInterface sampling X embed
      instanceCode elementCode
    have hLen := J.machineInput_length n (F n) (.inr (state, (c₁, c₂)))
    have hi := hInstance n (F n)
    have h₁ := hElement n (F n) c₁
    have h₂ := hElement n (F n) c₂
    change (J.machineInput n (F n) (.inr (state, (c₁, c₂)))).length =
      n + 3 + 2 * ((instanceCode n).encode (F n)).length +
        2 * ((requestCodeOfElement (elementCode n (F n))).encode
          (.inr (state, (c₁, c₂)))).length at hLen
    rw [requestCodeOfElement_guess_length] at hLen
    change (J.machineInput n (F n) (.inr (state, (c₁, c₂)))).length ≤
      size n * (state.length + 1)
    have h4 : 4 ≤ size n := by dsimp [size]; omega
    have hScale := Nat.mul_le_mul_right state.length h4
    dsimp [size] at *
    nlinarith

/-- Under uniform polynomial code-length bounds, the represented ElGamal
reachable class has a concrete finite-machine member: the machine that
halts immediately and returns the adapter's fallback. This establishes
nonemptiness of the source class without asserting ElGamal security. -/
theorem representedINDCPAElementPPTClass_halt_admissible
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (instanceCode : ∀ n, Machine.FiniteBitEncoding (X n))
    (elementCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding ((embed n x).params.Element))
    (instanceSize elementSize : Nat → Nat)
    (hInstance : ∀ n (x : X n),
      ((instanceCode n).encode x).length ≤ instanceSize n)
    (hElement : ∀ n (x : X n) (e : (embed n x).params.Element),
      ((elementCode n x).encode e).length ≤ elementSize n)
    (hInstancePoly : PolynomiallyBounded instanceSize)
    (hElementPoly : PolynomiallyBounded elementSize)
    (F : (n : Nat) → X n) :
    (representedINDCPAElementPPTClass sampling X embed instanceCode
      elementCode).admissible F
      ((representedINDCPAElementInterface sampling X embed instanceCode
        elementCode).realizeFamily F [.halt] (fun _ => 1)) := by
  obtain ⟨size, hSizePoly, hChoose, hGuess⟩ :=
    representedINDCPAElement_inputSizeLaws sampling X embed instanceCode
      elementCode instanceSize elementSize hInstance hElement
      hInstancePoly hElementPoly F
  refine ⟨[.halt], (fun _ => 1), size, PolynomiallyBounded.const 1,
    Machine.haltInstruction_haltsWithin, hSizePoly, ?_, ?_, rfl⟩
  · exact hChoose
  · exact hGuess

/-- Finite input/output protocol for DDH on the same represented instances. -/
noncomputable def representedDDHInterface
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (instanceCode : ∀ n, Machine.FiniteBitEncoding (X n))
    (tripleCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding
        ((embed n x).params.Element × (embed n x).params.Element ×
          (embed n x).params.Element)) :
    Machine.MachineAdversaryInterface
      (representedDDHGoal sampling X embed) :=
  Machine.ddhReindexedInterface (concreteDDHSemantics sampling) X
    (fun n x => (embed n x).params) instanceCode tripleCode

/-- The present all-request input-size condition makes the directly encoded
two-stage ElGamal IND-CPA class empty whenever a ciphertext exists. This
pinpoints why `representedINDCPAInterface.pptClass` cannot instantiate a
useful security theorem. `representedINDCPAReachablePPTClass` instead bounds
the states returned by `choose`; a machine simulator certificate for that
class remains a separate obligation. -/
theorem representedINDCPAInterface_pptClass_empty
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (instanceCode : ∀ n, Machine.FiniteBitEncoding (X n))
    (requestCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding
        ((embed n x).toElGamalInstance.scheme.PublicKey ⊕
          (List Bool × (embed n x).toElGamalInstance.scheme.Ciphertext)))
    (responseCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding
        (((embed n x).toElGamalInstance.scheme.Message ×
          (embed n x).toElGamalInstance.scheme.Message × List Bool) ⊕ Bool))
    (defaultMessage : ∀ n (x : X n),
      (embed n x).toElGamalInstance.scheme.Message)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (n : Nat)
    (ciphertext : (embed n (F n)).toElGamalInstance.scheme.Ciphertext)
    (A : AdversaryFamily (representedINDCPAGoal sampling X embed) F) :
    ¬ (representedINDCPAInterface sampling X embed instanceCode requestCode
      responseCode defaultMessage).pptClass.admissible F A := by
  exact Machine.indCPAReindexedInterface_pptClass_empty
    concreteINDCPASemantics X
    (fun n x => (embed n x).toElGamalInstance.scheme)
    instanceCode requestCode responseCode defaultMessage F n ciphertext A

end ElGamal
