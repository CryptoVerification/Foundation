import Foundation.Crypto.Semantics.Machine.PPT
import Foundation.Crypto.Semantics.Machine.Encoding
import Foundation.Assumptions.DDH.DDH
import Foundation.Notions.PKE.INDCPA.Goal
import Mathlib.Data.Set.Finite.List

namespace Machine

open Foundation.Probability

/-- No injective finite-bit encoding can assign a common length bound to
requests containing an arbitrary bitstring state. This is the input-size
obstruction for a two-stage IND-CPA protocol with unrestricted state. -/
theorem no_uniform_code_length_for_state
    {α β : Type*} (E : FiniteBitEncoding (β ⊕ (List Bool × α)))
    (a : α) :
    ¬ ∃ limit : Nat, ∀ state : List Bool,
      (E.encode (.inr (state, a))).length ≤ limit := by
  rintro ⟨limit, hLimit⟩
  let f : List Bool → {bits : List Bool // bits.length ≤ limit} :=
    fun state => ⟨E.encode (.inr (state, a)), hLimit state⟩
  have hFiniteCode : Finite {bits : List Bool // bits.length ≤ limit} :=
    (List.finite_length_le Bool limit).to_subtype
  have hInjective : Function.Injective f := by
    intro x y h
    have hCode : E.encode (.inr (x, a)) = E.encode (.inr (y, a)) :=
      congrArg Subtype.val h
    have hRequest := E.encode_injective hCode
    exact congrArg Prod.fst (Sum.inr.inj hRequest)
  have hFiniteState : Finite (List Bool) :=
    @Finite.of_injective (List Bool)
      {bits : List Bool // bits.length ≤ limit} hFiniteCode f hInjective
  exact hFiniteState.false

/-- A DDH distinguisher protocol: a machine reads three encoded group
elements and returns one bit. Parameter and element encodings are explicit
external inputs, rather than being inferred from algebraic DDH syntax. -/
def ddhInterface (S : DDHSemantics ProbComp)
    (parameterCode : FiniteBitEncoding DDHParameters)
    (tripleCode : ∀ params : DDHParameters,
      FiniteBitEncoding (params.Element × params.Element × params.Element)) :
    MachineAdversaryInterface (DDH ProbComp S) where
  Request := fun _ params => params.Element × params.Element × params.Element
  Response := fun _ _ => Bool
  instanceEncoding := fun _ => parameterCode
  requestEncoding := fun _ params => tripleCode params
  responseEncoding := fun _ _ => FiniteBitEncoding.bool
  fallback := fun _ _ => false
  assemble := fun _ _ respond =>
    ⟨fun x y z => respond (x, y, z)⟩

/-- DDH over a finitely encoded instance representation. The adapter sees a
code for the current represented instance, not a mathematical encoding of
every possible `DDHParameters` object. -/
def ddhReindexedInterface (S : DDHSemantics ProbComp)
    (X : Nat → Type 1) (params : ∀ n, X n → DDHParameters)
    (instanceCode : ∀ n, FiniteBitEncoding (X n))
    (tripleCode : ∀ n (x : X n),
      FiniteBitEncoding ((params n x).Element ×
        (params n x).Element × (params n x).Element)) :
    MachineAdversaryInterface ((DDH ProbComp S).reindex X params) where
  Request := fun n x => (params n x).Element ×
    (params n x).Element × (params n x).Element
  Response := fun _ _ => Bool
  instanceEncoding := fun n => instanceCode n
  requestEncoding := fun n x => tripleCode n x
  responseEncoding := fun _ _ => FiniteBitEncoding.bool
  fallback := fun _ _ => false
  assemble := fun _ _ respond =>
    ⟨fun x y z => respond (x, y, z)⟩

/-- Polynomial codes for the current represented DDH instance and challenge
triple give a polynomial bound on the complete framed machine input. The
bound includes the unary security parameter and both frame delimiters. -/
def ddhReindexedInputSizeBound
    (S : DDHSemantics ProbComp)
    (X : Nat → Type 1) (params : ∀ n, X n → DDHParameters)
    (instanceCode : ∀ n, FiniteBitEncoding (X n))
    (tripleCode : ∀ n (x : X n),
      FiniteBitEncoding ((params n x).Element ×
        (params n x).Element × (params n x).Element))
    (F : (n : Nat) → X n)
    (instanceSize tripleSize : Nat → Nat)
    (hInstance : ∀ n, ((instanceCode n).encode (F n)).length ≤ instanceSize n)
    (hTriple : ∀ n (triple : (params n (F n)).Element ×
      (params n (F n)).Element × (params n (F n)).Element),
      ((tripleCode n (F n)).encode triple).length ≤ tripleSize n) :
    (ddhReindexedInterface S X params instanceCode tripleCode).InputSizeBound F where
  limit n := n + 3 + 2 * instanceSize n + 2 * tripleSize n
  length_le := by
    intro n triple
    have hi := hInstance n
    have ht := hTriple n triple
    simp only [MachineAdversaryInterface.machineInput,
      ddhReindexedInterface, encodeSecurityParameter, frame,
      List.length_append, List.length_replicate, List.length_cons,
      List.length_nil] at *
    omega

theorem ddhReindexedInputSizeBound_polynomial
    (S : DDHSemantics ProbComp)
    (X : Nat → Type 1) (params : ∀ n, X n → DDHParameters)
    (instanceCode : ∀ n, FiniteBitEncoding (X n))
    (tripleCode : ∀ n (x : X n),
      FiniteBitEncoding ((params n x).Element ×
        (params n x).Element × (params n x).Element))
    (F : (n : Nat) → X n)
    (instanceSize tripleSize : Nat → Nat)
    (hInstance : ∀ n, ((instanceCode n).encode (F n)).length ≤ instanceSize n)
    (hTriple : ∀ n (triple : (params n (F n)).Element ×
      (params n (F n)).Element × (params n (F n)).Element),
      ((tripleCode n (F n)).encode triple).length ≤ tripleSize n)
    (hInstancePoly : PolynomiallyBounded instanceSize)
    (hTriplePoly : PolynomiallyBounded tripleSize) :
    PolynomiallyBounded
      (ddhReindexedInputSizeBound S X params instanceCode tripleCode F
        instanceSize tripleSize hInstance hTriple).limit := by
  exact (((PolynomiallyBounded.id.add (PolynomiallyBounded.const 3)).add
    ((PolynomiallyBounded.const 2).mul hInstancePoly)).add
      ((PolynomiallyBounded.const 2).mul hTriplePoly))

/-- Uniform polynomial element codes supply an explicit triple code and a
polynomial complete-input bound for every represented DDH instance family.
This proves an input representation property only; it does not implement any
group operation as machine instructions. -/
theorem ddhReindexedTripleInputSizeBound
    (S : DDHSemantics ProbComp)
    (X : Nat → Type 1) (params : ∀ n, X n → DDHParameters)
    (instanceCode : ∀ n, FiniteBitEncoding (X n))
    (elementCode : ∀ n (x : X n),
      FiniteBitEncoding ((params n x).Element))
    (instanceSize elementSize : Nat → Nat)
    (hInstance : ∀ n (x : X n),
      ((instanceCode n).encode x).length ≤ instanceSize n)
    (hElement : ∀ n (x : X n) (e : (params n x).Element),
      ((elementCode n x).encode e).length ≤ elementSize n)
    (hInstancePoly : PolynomiallyBounded instanceSize)
    (hElementPoly : PolynomiallyBounded elementSize) :
    ∀ F : (n : Nat) → X n,
      ∃ size : (ddhReindexedInterface S X params instanceCode
        (fun n x => (elementCode n x).triple)).InputSizeBound F,
        PolynomiallyBounded size.limit := by
  intro F
  let tripleSize : Nat → Nat := fun n => 5 * elementSize n + 2
  have hTriplePoly : PolynomiallyBounded tripleSize := by
    exact ((PolynomiallyBounded.const 5).mul hElementPoly).add
      (PolynomiallyBounded.const 2)
  have hTriple : ∀ n (triple : (params n (F n)).Element ×
      (params n (F n)).Element × (params n (F n)).Element),
      (((elementCode n (F n)).triple).encode triple).length ≤ tripleSize n := by
    intro n triple
    rcases triple with ⟨x, y, z⟩
    exact (elementCode n (F n)).triple_encode_length_le
      (elementSize n) (hElement n (F n)) x y z
  let size := ddhReindexedInputSizeBound S X params instanceCode
    (fun n x => (elementCode n x).triple) F instanceSize tripleSize
    (fun n => hInstance n (F n)) hTriple
  exact ⟨size, ddhReindexedInputSizeBound_polynomial S X params
    instanceCode (fun n x => (elementCode n x).triple) F
    instanceSize tripleSize (fun n => hInstance n (F n)) hTriple
    hInstancePoly hTriplePoly⟩

/-- A two-stage IND-CPA protocol using finite bitstring state. The same
machine code handles tagged `choose` and `guess` requests; every invocation
gets fresh machine random bits. Encoding the PKE instance, stage requests,
and stage responses is an explicit premise. This does not make arbitrary PKE
schemes finitely representable or their operations efficient. -/
noncomputable def indCPAInterface (S : INDCPASemantics ProbComp)
    (schemeCode : FiniteBitEncoding (PKE ProbComp))
    (requestCode : ∀ scheme : PKE ProbComp,
      FiniteBitEncoding (scheme.PublicKey ⊕ (List Bool × scheme.Ciphertext)))
    (responseCode : ∀ scheme : PKE ProbComp,
      FiniteBitEncoding
        ((scheme.Message × scheme.Message × List Bool) ⊕ Bool))
    (defaultMessage : ∀ scheme : PKE ProbComp, scheme.Message) :
    MachineAdversaryInterface (INDCPA ProbComp S) where
  Request := fun _ scheme => scheme.PublicKey ⊕ (List Bool × scheme.Ciphertext)
  Response := fun _ scheme =>
    (scheme.Message × scheme.Message × List Bool) ⊕ Bool
  instanceEncoding := fun _ => schemeCode
  requestEncoding := fun _ scheme => requestCode scheme
  responseEncoding := fun _ scheme => responseCode scheme
  fallback := fun _ _ => .inr false
  assemble := fun _ scheme respond =>
    { State := List Bool
      choose := fun pk =>
        (respond (.inl pk)).map fun answer =>
          match answer with
          | .inl messages => messages
          | .inr _ => (defaultMessage scheme, defaultMessage scheme, [])
      guess := fun state ciphertext =>
        (respond (.inr (state, ciphertext))).map fun answer =>
          match answer with
          | .inl _ => false
          | .inr bit => bit }

/-- The two-stage IND-CPA adapter restricted to a chosen, finitely encoded
instance representation. This avoids requiring a bit encoding for every
mathematical `PKE ProbComp` object. The representation and the stage value
encodings remain explicit premises; their computation costs are not certified
by this adapter. -/
noncomputable def indCPAReindexedInterface (S : INDCPASemantics ProbComp)
    (X : Nat → Type 1) (scheme : ∀ n, X n → PKE ProbComp)
    (instanceCode : ∀ n, FiniteBitEncoding (X n))
    (requestCode : ∀ n (x : X n),
      FiniteBitEncoding ((scheme n x).PublicKey ⊕
        (List Bool × (scheme n x).Ciphertext)))
    (responseCode : ∀ n (x : X n),
      FiniteBitEncoding (((scheme n x).Message ×
        (scheme n x).Message × List Bool) ⊕ Bool))
    (defaultMessage : ∀ n (x : X n), (scheme n x).Message) :
    MachineAdversaryInterface
      ((INDCPA ProbComp S).reindex X scheme) where
  Request := fun n x => (scheme n x).PublicKey ⊕
    (List Bool × (scheme n x).Ciphertext)
  Response := fun n x =>
    ((scheme n x).Message × (scheme n x).Message × List Bool) ⊕ Bool
  instanceEncoding := fun n => instanceCode n
  requestEncoding := fun n x => requestCode n x
  responseEncoding := fun n x => responseCode n x
  fallback := fun _ _ => .inr false
  assemble := fun n x respond =>
    { State := List Bool
      choose := fun pk =>
        (respond (.inl pk)).map fun answer =>
          match answer with
          | .inl messages => messages
          | .inr _ => (defaultMessage n x, defaultMessage n x, [])
      guess := fun state ciphertext =>
        (respond (.inr (state, ciphertext))).map fun answer =>
          match answer with
          | .inl _ => false
          | .inr bit => bit }

/-- With any available ciphertext, the unrestricted IND-CPA guess request
admits every finite bitstring as state. Its injective request code therefore
has no common length bound at that parameter. The current `InputSizeBound`
quantifies over all requests, so this protocol cannot supply one. A machine
PPT theorem for IND-CPA needs a bound on reachable requests instead. -/
theorem indCPAReindexedInterface_no_inputSizeBound
    (S : INDCPASemantics ProbComp)
    (X : Nat → Type 1) (scheme : ∀ n, X n → PKE ProbComp)
    (instanceCode : ∀ n, FiniteBitEncoding (X n))
    (requestCode : ∀ n (x : X n),
      FiniteBitEncoding ((scheme n x).PublicKey ⊕
        (List Bool × (scheme n x).Ciphertext)))
    (responseCode : ∀ n (x : X n),
      FiniteBitEncoding (((scheme n x).Message ×
        (scheme n x).Message × List Bool) ⊕ Bool))
    (defaultMessage : ∀ n (x : X n), (scheme n x).Message)
    (F : InstanceFamily ((INDCPA ProbComp S).reindex X scheme))
    (n : Nat) (ciphertext : (scheme n (F n)).Ciphertext) :
    ¬ Nonempty ((indCPAReindexedInterface S X scheme instanceCode requestCode
      responseCode defaultMessage).InputSizeBound F) := by
  let J := indCPAReindexedInterface S X scheme instanceCode
    requestCode responseCode defaultMessage
  rintro ⟨size⟩
  have hCode : ∀ state : List Bool,
      ((requestCode n (F n)).encode (.inr (state, ciphertext))).length ≤
        size.limit n := by
    intro state
    have hPart := J.requestCode_length_le_machineInput n (F n)
      (.inr (state, ciphertext))
    have hWhole := size.length_le n (.inr (state, ciphertext))
    exact hPart.trans hWhole
  exact no_uniform_code_length_for_state (requestCode n (F n))
    ciphertext ⟨size.limit n, hCode⟩

/-- Consequently, the current all-request `pptClass` is empty for a normal
two-stage IND-CPA interface with a ciphertext at one parameter. This theorem
records a genuine specification gap, not a cryptographic insecurity result. -/
theorem indCPAReindexedInterface_pptClass_empty
    (S : INDCPASemantics ProbComp)
    (X : Nat → Type 1) (scheme : ∀ n, X n → PKE ProbComp)
    (instanceCode : ∀ n, FiniteBitEncoding (X n))
    (requestCode : ∀ n (x : X n),
      FiniteBitEncoding ((scheme n x).PublicKey ⊕
        (List Bool × (scheme n x).Ciphertext)))
    (responseCode : ∀ n (x : X n),
      FiniteBitEncoding (((scheme n x).Message ×
        (scheme n x).Message × List Bool) ⊕ Bool))
    (defaultMessage : ∀ n (x : X n), (scheme n x).Message)
    (F : InstanceFamily ((INDCPA ProbComp S).reindex X scheme))
    (n : Nat) (ciphertext : (scheme n (F n)).Ciphertext)
    (A : AdversaryFamily ((INDCPA ProbComp S).reindex X scheme) F) :
    ¬ (indCPAReindexedInterface S X scheme instanceCode requestCode
      responseCode defaultMessage).pptClass.admissible F A := by
  intro h
  obtain ⟨_, _, size, _, _, _, _⟩ := h
  exact (indCPAReindexedInterface_no_inputSizeBound S X scheme
    instanceCode requestCode responseCode defaultMessage F n ciphertext)
    ⟨size⟩

end Machine
