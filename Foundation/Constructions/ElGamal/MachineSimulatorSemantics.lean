import Foundation.Constructions.ElGamal.MachineSimulatorRuntime

namespace ElGamal.RepresentedChooseNormalizer

open Machine Machine.GuardedCompiler

variable
  {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
  {X : Nat → Type 1} {embed : ∀ n, X n → ConcreteInstance sampling n}
  {M : RepresentedMachinePrimitives sampling X embed}

/-- The choose response of the existing represented adapter is exactly the
interpretation of the actual prepared source output PMF. Native execution
has halted, so the adapter's timeout fallback introduces no extra mass. -/
private theorem source_choose (source : Program) (q : Nat → Nat)
    (hSource : ∀ input, HaltsWithin source input (q input.length))
    (n : Nat) (x : X n) (first : (embed n x).params.Element) :
    let J := representedINDCPAElementInterface sampling X embed M.instanceCode M.elementCode
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let request := encodeSecurityParameter n ++ frame I ++ frame (false :: E.encode first)
    (J.assemble n x (J.responseWithin source q n x)).choose first =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => interpretChooseResponse E (embed n x).params.generator c.outputBits) := by
  dsimp only
  let request := encodeSecurityParameter n ++ frame ((M.instanceCode n).encode x) ++
    frame (false :: (M.elementCode n x).encode first)
  simp only [representedINDCPAElementInterface, representedINDCPAInterface,
    indCPAReindexedInterface, MachineAdversaryInterface.responseWithin,
    MachineAdversaryInterface.machineInput, requestCodeOfElement, FiniteBitEncoding.sum,
    PMF.map_comp]
  dsimp [representedINDCPAGoal, INDCPA, CryptoGoal.reindex]
  change (evalWithin source request (q request.length)).map _ = _
  rw [← preparedSource_evalOutput, PMF.map_comp]
  simp only [PMF.map]
  erw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  have hHalted := preparedSource_all_branches_halted source request (q request.length) (hSource request)
    c ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  simp only [Function.comp_def, hHalted, ↓reduceIte, Option.bind_some]
  cases hDecoded : (responseCodeOfElement (M.elementCode n x)).decode c.outputBits with
  | none =>
      erw [hDecoded]
      simp [interpretChooseResponse, hDecoded]
      rfl
  | some response =>
      cases response <;> erw [hDecoded] <;> simp [interpretChooseResponse, hDecoded] <;> rfl

/-- The guess response of the same source code agrees with native tagged
guess interpretation, on every raw reply including malformed encodings. -/
private theorem source_guess (source : Program) (q : Nat → Nat)
    (hSource : ∀ input, HaltsWithin source input (q input.length))
    (n : Nat) (x : X n) (state : List Bool) (second product : (embed n x).params.Element) :
    let J := representedINDCPAElementInterface sampling X embed M.instanceCode M.elementCode
    let request := guessFromProductRequest n ((M.instanceCode n).encode x) ((M.elementCode n x).encode second)
      state ((M.elementCode n x).encode product)
    (J.assemble n x (J.responseWithin source q n x)).guess state (second, product) =
      (evalConfigWithin source (preparedSource request) (q request.length)).map
        (fun c => taggedGuessValue c.outputBits) := by
  dsimp only
  let request := encodeSecurityParameter n ++ (frame ((M.instanceCode n).encode x) ++
    frame (true :: (FiniteBitEncoding.delimit state ++
      (FiniteBitEncoding.delimit ((M.elementCode n x).encode second) ++ (M.elementCode n x).encode product))))
  simp only [representedINDCPAElementInterface, representedINDCPAInterface,
    indCPAReindexedInterface, MachineAdversaryInterface.responseWithin,
    MachineAdversaryInterface.machineInput, requestCodeOfElement, FiniteBitEncoding.sum,
    FiniteBitEncoding.prod, FiniteBitEncoding.bitstring, PMF.map_comp, id_eq,
    List.append_assoc]
  simp only [guessFromProductRequest, List.append_assoc]
  dsimp [representedINDCPAGoal, INDCPA, CryptoGoal.reindex]
  change (evalWithin source request (q request.length)).map _ = _
  rw [← preparedSource_evalOutput, PMF.map_comp]
  simp only [PMF.map]
  erw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  have hHalted := preparedSource_all_branches_halted source request (q request.length) (hSource request)
    c ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
  simp only [Function.comp_def, hHalted, ↓reduceIte, Option.bind_some]
  rw [← interpretGuessResponse_eq_taggedGuessValue (M.elementCode n x)]
  cases hDecoded : (responseCodeOfElement (M.elementCode n x)).decode c.outputBits with
  | none =>
      erw [hDecoded]
      simp [interpretGuessResponse, hDecoded]
      rfl
  | some response =>
      cases response <;> erw [hDecoded] <;> simp [interpretGuessResponse, hDecoded] <;> rfl

/-- The complete simulator's output law, expressed in the existing bounded
output evaluator. Normalization, arithmetic and source scratch are executed
by the same finite code as in the full configuration theorem. -/
theorem nativeSimulator_evalWithin (N : RepresentedChooseNormalizer M) (source : Program) (q : Nat → Nat)
    (hSource : ∀ input, HaltsWithin source input (q input.length))
    (n : Nat) (x : X n) (first second last : (embed n x).params.Element) :
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let request := encodeSecurityParameter n ++ frame I ++ frame (false :: E.encode first)
    let messages := fun c : Configuration => interpretChooseResponse E (embed n x).params.generator c.outputBits
    let product := fun c (bit : Bool) => E.encode ((embed n x).params.mul
      (if bit then (messages c).2.1 else (messages c).1) last)
    evalWithin (N.simulatorCode source)
      (encodeSecurityParameter n ++ frame I ++
        frame (FiniteBitEncoding.delimit (E.encode first) ++ FiniteBitEncoding.delimit (E.encode second) ++ E.encode last))
      (N.simulatorBudget source q n x first second last) =
      (evalConfigWithin source (preparedSource request) (q request.length)).bind (fun c =>
        Foundation.Probability.sampleBit.bind (fun bit =>
          (evalConfigWithin source (preparedSource (guessFromProductRequest n I (E.encode second) (messages c).2.2 (product c bit)))
            (q (guessFromProductRequest n I (E.encode second) (messages c).2.2 (product c bit)).length)).map
              (fun d => some [taggedGuessValue d.outputBits == bit]))) := by
  dsimp only
  have h := congrArg (fun law : PMF (Bool × List Bool) =>
    law.map (fun result => if result.1 then some result.2 else none))
    (N.nativeSimulator_eval source q hSource n x first second last)
  simpa only [evalWithin, PMF.map_comp, PMF.map_bind, Function.comp_def, ↓reduceIte] using h

/-- Native simulation agrees with the Phase 11 DDH adversary construction,
using the existing source and target machine adapters. `targetBudget` only
has to halt this encoded request for this pointwise semantic equality; the
separate PPT theorem also has to provide polynomial all-input termination.
No abstract simulator/transformation certificate is assumed here. -/
theorem nativeSimulator_distinguish (N : RepresentedChooseNormalizer M) (source : Program)
    (q targetBudget : Nat → Nat) (hSource : ∀ input, HaltsWithin source input (q input.length))
    (n : Nat) (x : X n) (first second last : (embed n x).params.Element)
    (hTarget : HaltsWithin (N.simulatorCode source)
      (encodeSecurityParameter n ++ frame ((M.instanceCode n).encode x) ++
        frame (FiniteBitEncoding.delimit ((M.elementCode n x).encode first) ++
          FiniteBitEncoding.delimit ((M.elementCode n x).encode second) ++ (M.elementCode n x).encode last))
      (targetBudget (encodeSecurityParameter n ++ frame ((M.instanceCode n).encode x) ++
        frame (FiniteBitEncoding.delimit ((M.elementCode n x).encode first) ++
          FiniteBitEncoding.delimit ((M.elementCode n x).encode second) ++ (M.elementCode n x).encode last)).length)) :
    let JI := representedINDCPAElementInterface sampling X embed M.instanceCode M.elementCode
    let JD := representedDDHInterface sampling X embed M.instanceCode (fun n x => (M.elementCode n x).triple)
    (JD.assemble n x (JD.responseWithin (N.simulatorCode source) targetBudget n x)).distinguish first second last =
      (ddhAdversaryOfINDCPA Foundation.Probability.sampleBit (embed n x).toElGamalInstance
        (JI.assemble n x (JI.responseWithin source q n x))).distinguish first second last := by
  dsimp only
  let I := (M.instanceCode n).encode x
  let E := M.elementCode n x
  let input := encodeSecurityParameter n ++ (frame I ++
    frame (FiniteBitEncoding.delimit (E.encode first) ++ (FiniteBitEncoding.delimit (E.encode second) ++ E.encode last)))
  let request := encodeSecurityParameter n ++ (frame I ++ frame (false :: E.encode first))
  let messages := fun c : Configuration => interpretChooseResponse E (embed n x).params.generator c.outputBits
  let product := fun c (bit : Bool) => E.encode ((embed n x).params.mul
    (if bit then (messages c).2.1 else (messages c).1) last)
  simp only [representedDDHInterface, ddhReindexedInterface,
    MachineAdversaryInterface.responseWithin, MachineAdversaryInterface.machineInput,
    FiniteBitEncoding.triple, FiniteBitEncoding.prod, List.append_assoc]
  simp only [List.append_assoc] at hTarget
  change (evalWithin (N.simulatorCode source) input (targetBudget input.length)).map
    (fun bits => (bits.bind FiniteBitEncoding.bool.decode).getD false) = _
  have hNative : HaltsWithin (N.simulatorCode source) input
      (N.simulatorBudget source q n x first second last) := by
    simpa only [input, I, E, List.append_assoc] using
      N.nativeSimulator_haltsWithin source q hSource n x first second last
  rw [evalWithin_eq_of_haltsWithin (N.simulatorCode source) input _ _ hTarget hNative]
  have hEval := N.nativeSimulator_evalWithin source q hSource n x first second last
  simp only [List.append_assoc] at hEval
  rw [hEval]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.bind_some,
    FiniteBitEncoding.bool, Option.getD_some]
  change (evalConfigWithin source (preparedSource request) (q request.length)).bind
    (fun c => Foundation.Probability.sampleBit.bind (fun bit =>
      (evalConfigWithin source (preparedSource (guessFromProductRequest n I (E.encode second) (messages c).2.2 (product c bit)))
        (q (guessFromProductRequest n I (E.encode second) (messages c).2.2 (product c bit)).length)).map
          (fun d => taggedGuessValue d.outputBits == bit))) = _
  simp only [ddhAdversaryOfINDCPA, bind, pure]
  erw [source_choose source q hSource n x first, PMF.bind_map]
  simp only [List.append_assoc]
  congr 1
  funext c
  congr 1
  funext bit
  erw [show ElGamal.challengeCiphertext (embed n x).params
    (if bit then (messages c).2.1 else (messages c).1) second last =
      (second, (embed n x).params.mul (if bit then (messages c).2.1 else (messages c).1) last) from rfl,
    source_guess source q hSource n x (messages c).2.2 second _, PMF.bind_map]
  rfl

/-- Compatibility for the whole adversary family, obtained from the actual
native simulation law. Termination is required on every represented target
request. This is a realization theorem, not yet an all-bitstring PPT claim. -/
theorem nativeSimulator_realizes (N : RepresentedChooseNormalizer M)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (A : AdversaryFamily (representedINDCPAGoal sampling X embed) F)
    (source : Program) (q targetBudget : Nat → Nat)
    (hSource : ∀ input, HaltsWithin source input (q input.length))
    (hRealize : (representedINDCPAElementInterface sampling X embed M.instanceCode M.elementCode).Realizes
      F source q A)
    (hTarget : ∀ n (x : X n) (first second last : (embed n x).params.Element),
      let input := encodeSecurityParameter n ++ frame ((M.instanceCode n).encode x) ++
        frame (FiniteBitEncoding.delimit ((M.elementCode n x).encode first) ++
          FiniteBitEncoding.delimit ((M.elementCode n x).encode second) ++ (M.elementCode n x).encode last)
      HaltsWithin (N.simulatorCode source) input (targetBudget input.length)) :
    (representedDDHInterface sampling X embed M.instanceCode
      (fun n x => (M.elementCode n x).triple)).Realizes
      ((representedReduction sampling X embed).mapFamily F) (N.simulatorCode source) targetBudget
      ((representedReduction sampling X embed).mapAdversaryFamily F A) := by
  unfold MachineAdversaryInterface.Realizes at hRealize ⊢
  subst A
  funext n
  change DDHAdversary.mk _ = DDHAdversary.mk _
  congr 1
  funext first second last
  exact N.nativeSimulator_distinguish source q targetBudget hSource n (F n) first second last
    (hTarget n (F n) first second last)

/-- A polynomial source stopping profile produces a polynomial target
evaluation budget and the exact Phase 11 transformed adversary family.
The budget halts every represented DDH request by construction. Membership
in `pptClass` additionally requires the all-bitstring stopping certificate,
provided by `nativeSimulator_polynomialTime` and used below. No externally supplied
abstract program transformation is needed for this semantic construction. -/
theorem nativeSimulator_polynomial_realization (N : RepresentedChooseNormalizer M)
    (F : InstanceFamily (representedINDCPAGoal sampling X embed))
    (A : AdversaryFamily (representedINDCPAGoal sampling X embed) F)
    (source : Program) (q : Nat → Nat) (hPolynomial : PolynomiallyBounded q)
    (hSource : ∀ input, HaltsWithin source input (q input.length))
    (hRealize : (representedINDCPAElementInterface sampling X embed M.instanceCode M.elementCode).Realizes
      F source q A) :
    ∃ targetBudget : Nat → Nat, PolynomiallyBounded targetBudget ∧
      (representedDDHInterface sampling X embed M.instanceCode
        (fun n x => (M.elementCode n x).triple)).Realizes
        ((representedReduction sampling X embed).mapFamily F) (N.simulatorCode source) targetBudget
        ((representedReduction sampling X embed).mapAdversaryFamily F A) := by
  obtain ⟨coefficient, degree, hHalts⟩ :=
    N.nativeSimulator_haltsWithin_inputMonomial source q hPolynomial hSource
  let targetBudget : Nat → Nat := fun m => coefficient * (m + 1)^degree
  have hTargetPolynomial : PolynomiallyBounded targetBudget :=
    (PolynomiallyBounded.const coefficient).mul
      ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).pow degree)
  exact ⟨targetBudget, hTargetPolynomial,
    N.nativeSimulator_realizes F A source q targetBudget hSource hRealize hHalts⟩


/-- Native code and the explicit computational representation preserve the
nonvacuous reachable-request IND-CPA machine class. The target witness is
exactly `simulatorCode source`, with one all-input polynomial stopping
budget. Its semantic compatibility is the existing native simulation law,
and its DDH input-size bound follows from the representation lengths. -/
theorem nativeSimulator_preservesAdmissibility (N : RepresentedChooseNormalizer M) :
    (representedReduction sampling X embed).PreservesAdmissibility
      (representedINDCPAElementPPTClass sampling X embed M.instanceCode M.elementCode)
      (representedDDHInterface sampling X embed M.instanceCode
        (fun n x => (M.elementCode n x).triple)).pptClass := by
  constructor
  intro F A hA
  obtain ⟨source, q, _sourceSize, hPolynomial, hSource, _hSize, _hChoose, _hGuess, hRealize⟩ := hA
  obtain ⟨targetBudget, hTargetPolynomial, hTarget⟩ :=
    N.nativeSimulator_polynomialTime source q hPolynomial hSource
  obtain ⟨targetSize, hTargetSize⟩ := Machine.ddhReindexedTripleInputSizeBound
    (concreteDDHSemantics sampling) X (fun n x => (embed n x).params)
    M.instanceCode M.elementCode M.instanceCodeLength M.elementCodeLength
    M.instanceCode_length_le M.elementCode_length_le
    M.instanceCodeLength_polynomial M.elementCodeLength_polynomial
    ((representedReduction sampling X embed).mapFamily F)
  refine ⟨N.simulatorCode source, targetBudget, targetSize, hTargetPolynomial, hTarget, hTargetSize, ?_⟩
  exact N.nativeSimulator_realizes F A source q targetBudget hSource hRealize
    (fun n x first second last => hTarget _)

end ElGamal.RepresentedChooseNormalizer
