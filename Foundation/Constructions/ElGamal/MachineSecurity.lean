import Foundation.Constructions.ElGamal.ConcreteSecurity
import Foundation.Constructions.ElGamal.MachineRepresented
import Foundation.Machine.Security

namespace ElGamal

open Foundation.Probability

/-- Conditional machine-PPT security transport for the concrete ElGamal
reduction. The supplied `T` must contain an actual finite-code simulator,
its operational runtime bound, and the proof that its machine semantics
matches the Phase 11 reduction. `FiniteAlgebra` alone does not produce `T`:
encoded group operations and exact worst-case polynomial scalar sampling
remain separate computational obligations. -/
theorem secureINDCPA_of_secureDDH_machinePPT_of_transformation
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (JI : Machine.MachineAdversaryInterface
      (concreteINDCPAGoal sampling))
    (JD : Machine.MachineAdversaryInterface
      (DDH ProbComp (concreteDDHSemantics sampling)))
    (F : InstanceFamily (concreteINDCPAGoal sampling))
    (T : (concreteReduction sampling).MachineProgramTransformation JI JD)
    (hDDH : SecureOnWithin
      (DDH ProbComp (concreteDDHSemantics sampling))
      JD.pptClass ((concreteReduction sampling).mapFamily F)) :
    SecureOnWithin (concreteINDCPAGoal sampling) JI.pptClass F := by
  let R := concreteReduction sampling
  have hLoss : R.loss.PreservesNegligible := by
    change AdvantageBound.id.PreservesNegligible
    exact AdvantageBound.id_preservesNegligible
  exact R.secureOnWithin_machinePPT JI JD F T hLoss hDDH

/-- The same conditional transport on a finitely represented instance domain.
Here the machine interfaces need encode only `X n` and the protocol values at
represented instances. `T` still has to provide the actual finite-code DDH
simulator and its step bound: neither the reindexing nor `MachinePrimitives`
constructs that compiler. For the current unrestricted two-stage IND-CPA
adapter, `indCPAReindexedInterface_pptClass_empty` shows an additional
input-size obstruction: all-request bounds cannot cover arbitrary states.
This transport is currently a typing result. The separate
`representedINDCPAReachablePPTClass` models reachable states, but the
current `MachineProgramTransformation` theorem preserves only the older
all-request class. A simulator certificate for the reachable class is still
required before this transport states nonvacuous ElGamal security. -/
theorem secureRepresentedINDCPA_of_secureRepresentedDDH_machinePPT
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (JI : Machine.MachineAdversaryInterface
      (representedINDCPAGoal sampling X embed))
    (JD : Machine.MachineAdversaryInterface
      (representedDDHGoal sampling X embed))
    (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (T : (representedReduction sampling X embed).MachineProgramTransformation JI JD)
    (hDDH : SecureOnWithin
      (representedDDHGoal sampling X embed)
      JD.pptClass ((representedReduction sampling X embed).mapFamily F)) :
    SecureOnWithin (representedINDCPAGoal sampling X embed)
      JI.pptClass F := by
  let R := representedReduction sampling X embed
  have hLoss : R.loss.PreservesNegligible := by
    change AdvantageBound.id.PreservesNegligible
    exact AdvantageBound.id_preservesNegligible
  exact R.secureOnWithin_machinePPT JI JD F T hLoss hDDH

/-- Conditional transport for the reachable-request IND-CPA class. Unlike
the older all-request source class, this class has concrete finite-machine
members for suitable encodings. `T` must still certify a real finite-code
ElGamal-to-DDH simulator, and `hTargetSize` must bound encoded DDH requests.
Neither certificate is constructed from the mathematical group axioms. -/
theorem secureRepresentedINDCPA_of_secureRepresentedDDH_machineReachablePPT
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
      (fun n x => (embed n x).toElGamalInstance.scheme) responseCode)
    (JD : Machine.MachineAdversaryInterface
      (representedDDHGoal sampling X embed))
    (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (T : (representedReduction sampling X embed).MachineProgramSimulation
      (representedINDCPAInterface sampling X embed instanceCode requestCode
        responseCode defaultMessage) JD)
    (hTargetSize : ∀ G : InstanceFamily (representedINDCPAGoal sampling X embed),
      ∃ size : JD.InputSizeBound
          ((representedReduction sampling X embed).mapFamily G),
        PolynomiallyBounded size.limit)
    (hDDH : SecureOnWithin
      (representedDDHGoal sampling X embed)
      JD.pptClass ((representedReduction sampling X embed).mapFamily F)) :
    SecureOnWithin (representedINDCPAGoal sampling X embed)
      (representedINDCPAReachablePPTClass sampling X embed instanceCode
        requestCode responseCode defaultMessage hFaithful) F := by
  let R := representedReduction sampling X embed
  have hAdmissible : R.PreservesAdmissibility
      (representedINDCPAReachablePPTClass sampling X embed instanceCode
        requestCode responseCode defaultMessage hFaithful) JD.pptClass := by
    exact Machine.indCPAReindexedReachablePPTClass_preserved
      concreteINDCPASemantics X
      (fun n x => (embed n x).toElGamalInstance.scheme)
      instanceCode requestCode responseCode defaultMessage hFaithful
      R JD T hTargetSize
  have hLoss : R.loss.PreservesNegligible := by
    change AdvantageBound.id.PreservesNegligible
    exact AdvantageBound.id_preservesNegligible
  exact R.secureOnWithin
    (representedINDCPAReachablePPTClass sampling X embed instanceCode
      requestCode responseCode defaultMessage hFaithful) JD.pptClass F
    hAdmissible hLoss hDDH

/-- The target DDH input-size premise above follows from explicit uniform
polynomial encodings of represented instances and group elements. The
finite-code simulator certificate `T` remains an independent requirement. -/
theorem secureRepresentedINDCPA_of_secureRepresentedDDH_machineEncodedPPT
    (sampling : (n : Nat) → (params : DDHParameters) →
      Option (DDHFiniteSampling params))
    (X : Nat → Type 1)
    (embed : ∀ n, X n → ConcreteInstance sampling n)
    (instanceCode : ∀ n, Machine.FiniteBitEncoding (X n))
    (elementCode : ∀ n (x : X n),
      Machine.FiniteBitEncoding ((embed n x).params.Element))
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
      (fun n x => (embed n x).toElGamalInstance.scheme) responseCode)
    (instanceSize elementSize : Nat → Nat)
    (hInstance : ∀ n (x : X n),
      ((instanceCode n).encode x).length ≤ instanceSize n)
    (hElement : ∀ n (x : X n) (e : (embed n x).params.Element),
      ((elementCode n x).encode e).length ≤ elementSize n)
    (hInstancePoly : PolynomiallyBounded instanceSize)
    (hElementPoly : PolynomiallyBounded elementSize)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (T : (representedReduction sampling X embed).MachineProgramSimulation
      (representedINDCPAInterface sampling X embed instanceCode requestCode
        responseCode defaultMessage)
      (representedDDHInterface sampling X embed instanceCode
        (fun n x => (elementCode n x).triple)))
    (hDDH : SecureOnWithin
      (representedDDHGoal sampling X embed)
      (representedDDHInterface sampling X embed instanceCode
        (fun n x => (elementCode n x).triple)).pptClass
      ((representedReduction sampling X embed).mapFamily F)) :
    SecureOnWithin (representedINDCPAGoal sampling X embed)
      (representedINDCPAReachablePPTClass sampling X embed instanceCode
        requestCode responseCode defaultMessage hFaithful) F := by
  let JD := representedDDHInterface sampling X embed instanceCode
    (fun n x => (elementCode n x).triple)
  have hTargetSize : ∀ G : InstanceFamily
      (representedINDCPAGoal sampling X embed),
      ∃ size : JD.InputSizeBound
        ((representedReduction sampling X embed).mapFamily G),
        PolynomiallyBounded size.limit := by
    intro G
    exact Machine.ddhReindexedTripleInputSizeBound
      (concreteDDHSemantics sampling) X (fun n x => (embed n x).params)
      instanceCode elementCode instanceSize elementSize hInstance hElement
      hInstancePoly hElementPoly
      ((representedReduction sampling X embed).mapFamily G)
  exact secureRepresentedINDCPA_of_secureRepresentedDDH_machineReachablePPT
    sampling X embed instanceCode requestCode responseCode defaultMessage
    hFaithful JD F T hTargetSize hDDH

/-- The element-based adapters discharge the finite request/response coding
and decoder state-size premises of the preceding theorem. The remaining
`T` premise is the actual two-stage machine simulator certificate. The
`ProgramCompiler.twoCalls` constructor can emit two rebased copies of the
source code, but no wrapper with the required tape preparation, semantic
correctness, and runtime proof has yet been constructed. -/
theorem secureRepresentedINDCPA_of_secureRepresentedDDH_machineElementPPT
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
    (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (T : (representedReduction sampling X embed).MachineProgramSimulation
      (representedINDCPAElementInterface sampling X embed instanceCode elementCode)
      (representedDDHInterface sampling X embed instanceCode
        (fun n x => (elementCode n x).triple)))
    (hDDH : SecureOnWithin
      (representedDDHGoal sampling X embed)
      (representedDDHInterface sampling X embed instanceCode
        (fun n x => (elementCode n x).triple)).pptClass
      ((representedReduction sampling X embed).mapFamily F)) :
    SecureOnWithin (representedINDCPAGoal sampling X embed)
      (representedINDCPAElementPPTClass sampling X embed instanceCode
        elementCode) F := by
  exact secureRepresentedINDCPA_of_secureRepresentedDDH_machineEncodedPPT
    sampling X embed instanceCode elementCode
    (fun n x => requestCodeOfElement (elementCode n x))
    (fun n x => responseCodeOfElement (elementCode n x))
    (fun n x => (embed n x).params.generator)
    (responseCodeOfElement_chooseStateSizeFaithful sampling X embed elementCode)
    instanceSize elementSize hInstance hElement hInstancePoly hElementPoly
    F T hDDH

end ElGamal
