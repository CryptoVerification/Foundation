import Foundation.Constructions.ElGamal.MachineSimulator
import Foundation.Machine.PPT

namespace ElGamal.RepresentedChooseNormalizer

open Machine Machine.GuardedCompiler

variable
  {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
  {X : Nat → Type 1} {embed : ∀ n, X n → ConcreteInstance sampling n}
  {M : RepresentedMachinePrimitives sampling X embed}

private theorem monomial_profile {size : Nat → Nat} (hSize : PolynomiallyBounded size)
    (coefficient degree : Nat) : PolynomiallyBounded (fun n => coefficient * (size n + 1)^degree) :=
  (PolynomiallyBounded.const coefficient).mul ((hSize.add (PolynomiallyBounded.const 1)).pow degree)

private theorem time_le_at_length (q : Nat → Nat) (coefficient degree : Nat)
    (h : ∀ m, q m ≤ coefficient * (m + 1)^degree) {length limit : Nat} (hLength : length ≤ limit) :
    q length ≤ coefficient * (limit + 1)^degree :=
  (h length).trans (Nat.mul_le_mul_left coefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hLength 1) degree))

/-- The actual complete simulator budget on every encoded represented DDH
tuple has one polynomial majorant in the security parameter. This includes
every source choose branch, its retained scratch, normalization, both native
challenge choices, multiplication and guess. Only global monomial upper
bounds for time functions are used; the functions themselves need not be
monotone. The finite maximum over choose branches is bounded pointwise, so
its potentially exponential enumeration is not simulator execution.

This theorem concerns encoded tuples. It does not replace the separate
all-bitstring termination obligation in `Machine.PolynomialTime`. -/
theorem simulatorBudget_uniform_polynomial (N : RepresentedChooseNormalizer M)
    (source : Program) (q : Nat → Nat) (hSourcePolynomial : PolynomiallyBounded q) :
    ∃ budget : Nat → Nat, PolynomiallyBounded budget ∧
      ∀ n (x : X n) (first second last : (embed n x).params.Element),
        N.simulatorBudget source q n x first second last ≤ budget n := by
  obtain ⟨cSource, kSource, hSource⟩ :=
    MachineAdversaryInterface.global_monomial_of_polynomiallyBounded hSourcePolynomial
  obtain ⟨cNormalize, kNormalize, hNormalize⟩ :=
    MachineAdversaryInterface.global_monomial_of_polynomiallyBounded N.budget_polynomial
  obtain ⟨cMultiply, kMultiply, hMultiply⟩ :=
    MachineAdversaryInterface.global_monomial_of_polynomiallyBounded M.multiplyBudget_polynomial
  let chooseLength := fun n => n + 2 * M.instanceCodeLength n + 2 * M.elementCodeLength n + 5
  let ddhLength := fun n => n + 2 * M.instanceCodeLength n + 10 * M.elementCodeLength n + 7
  let chooseTime := fun n => cSource * (chooseLength n + 1)^kSource
  let storage := fun n => 2 * chooseLength n + 2 + chooseTime n
  let normalizeLength := fun n => n + 2 * M.instanceCodeLength n + 2 * storage n + 3
  let multiplyLength := fun n => n + 2 * M.instanceCodeLength n + 4 * M.elementCodeLength n + 4
  let guessLength := fun n => n + 2 * M.instanceCodeLength n + 4 * storage n + 6 * M.elementCodeLength n + 9
  let normalizeTime := fun n => cNormalize * (normalizeLength n + 1)^kNormalize
  let multiplyTime := fun n => cMultiply * (multiplyLength n + 1)^kMultiply
  let guessTime := fun n => cSource * (guessLength n + 1)^kSource
  let payloadSize := fun n => n + M.instanceCodeLength n + 7 * M.elementCodeLength n + chooseLength n + 3 * storage n + 1
  let tailTime := fun n => normalizeTime n + 2 * multiplyTime n + 2 * guessTime n + 1
  let tailBudget := fun n => 1300000 * (payloadSize n + normalizeTime n) * (tailTime n)^2
  let budget := fun n => 300 * (ddhLength n + 1) * (chooseTime n + 1)^2 + (tailBudget n + 1)
  have hBase : PolynomiallyBounded (fun n => n + 2 * M.instanceCodeLength n) :=
    PolynomiallyBounded.id.add ((PolynomiallyBounded.const 2).mul M.instanceCodeLength_polynomial)
  have hChooseLength : PolynomiallyBounded chooseLength :=
    (hBase.add ((PolynomiallyBounded.const 2).mul M.elementCodeLength_polynomial)).add (PolynomiallyBounded.const 5)
  have hDDHLength : PolynomiallyBounded ddhLength :=
    (hBase.add ((PolynomiallyBounded.const 10).mul M.elementCodeLength_polynomial)).add (PolynomiallyBounded.const 7)
  have hChooseTime : PolynomiallyBounded chooseTime := monomial_profile hChooseLength _ _
  have hStorage : PolynomiallyBounded storage :=
    (((PolynomiallyBounded.const 2).mul hChooseLength).add (PolynomiallyBounded.const 2)).add hChooseTime
  have hNormalizeLength : PolynomiallyBounded normalizeLength :=
    (hBase.add ((PolynomiallyBounded.const 2).mul hStorage)).add (PolynomiallyBounded.const 3)
  have hMultiplyLength : PolynomiallyBounded multiplyLength :=
    (hBase.add ((PolynomiallyBounded.const 4).mul M.elementCodeLength_polynomial)).add (PolynomiallyBounded.const 4)
  have hGuessLength : PolynomiallyBounded guessLength :=
    ((hBase.add ((PolynomiallyBounded.const 4).mul hStorage)).add
      ((PolynomiallyBounded.const 6).mul M.elementCodeLength_polynomial)).add (PolynomiallyBounded.const 9)
  have hNormalizeTime : PolynomiallyBounded normalizeTime := monomial_profile hNormalizeLength _ _
  have hMultiplyTime : PolynomiallyBounded multiplyTime := monomial_profile hMultiplyLength _ _
  have hGuessTime : PolynomiallyBounded guessTime := monomial_profile hGuessLength _ _
  have hPayload : PolynomiallyBounded payloadSize :=
    ((((PolynomiallyBounded.id.add M.instanceCodeLength_polynomial).add
      ((PolynomiallyBounded.const 7).mul M.elementCodeLength_polynomial)).add hChooseLength).add
      ((PolynomiallyBounded.const 3).mul hStorage)).add (PolynomiallyBounded.const 1)
  have hTailTime : PolynomiallyBounded tailTime :=
    ((hNormalizeTime.add ((PolynomiallyBounded.const 2).mul hMultiplyTime)).add
      ((PolynomiallyBounded.const 2).mul hGuessTime)).add (PolynomiallyBounded.const 1)
  have hTailBudget : PolynomiallyBounded tailBudget :=
    ((PolynomiallyBounded.const 1300000).mul (hPayload.add hNormalizeTime)).mul (hTailTime.pow 2)
  have hBudget : PolynomiallyBounded budget :=
    (((PolynomiallyBounded.const 300).mul (hDDHLength.add (PolynomiallyBounded.const 1))).mul
      ((hChooseTime.add (PolynomiallyBounded.const 1)).pow 2)).add (hTailBudget.add (PolynomiallyBounded.const 1))
  refine ⟨budget, hBudget, ?_⟩
  intro n x first second last
  let I := (M.instanceCode n).encode x
  let E := M.elementCode n x
  let request := encodeSecurityParameter n ++ frame I ++ frame (false :: E.encode first)
  let messages := fun c : Configuration => interpretChooseResponse E (embed n x).params.generator c.outputBits
  let product := fun c (bit : Bool) => E.encode ((embed n x).params.mul
    (if bit then (messages c).2.1 else (messages c).1) last)
  have hI : I.length ≤ M.instanceCodeLength n := M.instanceCode_length_le n x
  have hElement : ∀ a, (E.encode a).length ≤ M.elementCodeLength n := M.elementCode_length_le n x
  have hFirst := hElement first
  have hSecond := hElement second
  have hLast := hElement last
  have hRequest : request.length ≤ chooseLength n := by
    dsimp only [request, chooseLength]
    simp only [encodeSecurityParameter, frame, List.length_append, List.length_cons,
      List.length_replicate, List.length_nil]
    omega
  have hChooseTimeBound : q request.length ≤ chooseTime n := time_le_at_length q _ _ hSource hRequest
  have hDDHInput : (encodeSecurityParameter n ++ frame I ++
      frame (FiniteBitEncoding.delimit (E.encode first) ++ FiniteBitEncoding.delimit (E.encode second) ++ E.encode last)).length ≤
      ddhLength n := by
    dsimp only [ddhLength]
    simp only [encodeSecurityParameter, frame, List.length_append, List.length_cons,
      List.length_replicate, List.length_nil, FiniteBitEncoding.delimit_length]
    omega
  have hTail : N.simulatorTailBudget source q n x first second last ≤ tailBudget n := by
    apply chooseChallengeTailBudget_le
    intro c hc
    have hSizes := preparedChooseBranch_size_le source request (q request.length) c hc
    have hStore : sourceStorage c ≤ storage n := by dsimp only [storage]; omega
    have hReply : c.outputBits.length ≤ storage n := by dsimp only [storage]; omega
    have hState : (messages c).2.2.length ≤ storage n :=
      (interpretChooseResponse_state_length_le E (embed n x).params.generator c.outputBits).trans hReply
    have hMessage₀ := hElement (messages c).1
    have hMessage₁ := hElement (messages c).2.1
    have hProduct : ∀ bit : Bool, (product c bit).length ≤ M.elementCodeLength n := by
      intro bit
      exact hElement _
    let normalRequest := encodeSecurityParameter n ++ frame I ++ frame c.outputBits
    let selected := fun bit : Bool => E.encode (if bit then (messages c).2.1 else (messages c).1)
    let multiplyRequest := fun bit => encodeSecurityParameter n ++ frame I ++ frame (selected bit) ++ frame (E.encode last)
    let guessRequest := fun bit => guessFromProductRequest n I (E.encode second) (messages c).2.2 (product c bit)
    have hNormalLength : normalRequest.length ≤ normalizeLength n := by
      dsimp only [normalRequest, normalizeLength]
      simp only [encodeSecurityParameter, frame, List.length_append, List.length_cons,
        List.length_replicate, List.length_nil]
      omega
    have hMultiplyLength (bit : Bool) : (multiplyRequest bit).length ≤ multiplyLength n := by
      have hSelected : (selected bit).length ≤ M.elementCodeLength n := by cases bit <;> exact hElement _
      dsimp only [multiplyRequest, multiplyLength]
      simp only [encodeSecurityParameter, frame, List.length_append, List.length_cons,
        List.length_replicate, List.length_nil]
      omega
    have hGuessLength (bit : Bool) : (guessRequest bit).length ≤ guessLength n := by
      have hProductBit := hProduct bit
      dsimp only [guessRequest, guessFromProductRequest, guessLength]
      simp only [encodeSecurityParameter, frame, List.length_append, List.length_cons,
        List.length_replicate, List.length_nil, FiniteBitEncoding.delimit_length]
      omega
    have hNT : N.budget normalRequest.length ≤ normalizeTime n := time_le_at_length _ _ _ hNormalize hNormalLength
    have hMT (bit : Bool) : M.multiplyBudget (multiplyRequest bit).length ≤ multiplyTime n :=
      time_le_at_length _ _ _ hMultiply (hMultiplyLength bit)
    have hGT (bit : Bool) : q (guessRequest bit).length ≤ guessTime n :=
      time_le_at_length _ _ _ hSource (hGuessLength bit)
    have hPayloadSize : n + I.length + (E.encode first).length + (E.encode second).length + (E.encode last).length +
        request.length + c.outputBits.length + (E.encode (messages c).1).length + (E.encode (messages c).2.1).length +
        (messages c).2.2.length + (product c false).length + (product c true).length + sourceStorage c + 1 ≤ payloadSize n := by
      have hPFalse := hProduct false
      have hPTrue := hProduct true
      dsimp only [payloadSize]
      omega
    have hTimeBound : N.budget normalRequest.length + M.multiplyBudget (multiplyRequest false).length +
        M.multiplyBudget (multiplyRequest true).length + q (guessRequest false).length + q (guessRequest true).length + 1 ≤ tailTime n := by
      have hMF := hMT false
      have hMT := hMT true
      have hGF := hGT false
      have hGT := hGT true
      dsimp only [tailTime]
      omega
    have h := chooseChallengeBranchBudget_bound N.budget M.multiplyBudget q request n I
      (E.encode first) (E.encode second) (E.encode last)
      (fun c => E.encode (messages c).1) (fun c => E.encode (messages c).2.1) (fun c => (messages c).2.2) product c
    dsimp only at h
    apply h.trans
    change 1300000 * _ * _^2 ≤ 1300000 * (payloadSize n + normalizeTime n) * (tailTime n)^2
    apply Nat.mul_le_mul
    · apply Nat.mul_le_mul_left
      exact Nat.add_le_add hPayloadSize hNT
    · apply Nat.pow_le_pow_left _ 2
      simpa only [normalRequest, multiplyRequest, selected, guessRequest, apply_ite] using hTimeBound
  have hChoose := chooseTraceBudget_bound q n I (E.encode first)
    (FiniteBitEncoding.delimit (E.encode second) ++ E.encode last)
  have hChooseBound : chooseTraceBudget q n I (E.encode first)
      (FiniteBitEncoding.delimit (E.encode second) ++ E.encode last) ≤
      300 * (ddhLength n + 1) * (chooseTime n + 1)^2 := by
    apply hChoose.trans
    apply Nat.mul_le_mul
    · apply Nat.mul_le_mul_left
      simpa only [List.append_assoc] using Nat.add_le_add_right hDDHInput 1
    · exact Nat.pow_le_pow_left (Nat.add_le_add_right hChooseTimeBound 1) 2
  exact Nat.add_le_add hChooseBound (Nat.add_le_add_right hTail 1)

/-- One monomial stopping function of total input length works on every
represented encoded tuple. The constants do not vary with the security
parameter or tuple, and the simulator code itself is unchanged. This is a
valid-protocol-input result; malformed bitstrings still require a separate
proof before claiming `Machine.PolynomialTime` for the simulator. -/
theorem nativeSimulator_haltsWithin_inputMonomial (N : RepresentedChooseNormalizer M)
    (source : Program) (q : Nat → Nat) (hSourcePolynomial : PolynomiallyBounded q)
    (hSource : ∀ input, HaltsWithin source input (q input.length)) :
    ∃ coefficient degree : Nat,
      ∀ n (x : X n) (first second last : (embed n x).params.Element),
        let input := encodeSecurityParameter n ++ frame ((M.instanceCode n).encode x) ++
          frame (FiniteBitEncoding.delimit ((M.elementCode n x).encode first) ++
            FiniteBitEncoding.delimit ((M.elementCode n x).encode second) ++ (M.elementCode n x).encode last)
        HaltsWithin (N.simulatorCode source) input (coefficient * (input.length + 1)^degree) := by
  obtain ⟨budget, hBudget, hLimit⟩ := N.simulatorBudget_uniform_polynomial source q hSourcePolynomial
  obtain ⟨coefficient, degree, hGlobal⟩ := MachineAdversaryInterface.global_monomial_of_polynomiallyBounded hBudget
  refine ⟨coefficient, degree, ?_⟩
  intro n x first second last
  dsimp only
  apply (N.nativeSimulator_haltsWithin source q hSource n x first second last).mono
  apply (hLimit n x first second last).trans
  apply (hGlobal n).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left _ degree
  simp only [encodeSecurityParameter, frame, List.length_append, List.length_cons,
    List.length_replicate, List.length_nil, FiniteBitEncoding.delimit_length]
  omega


/-- The syntactically constructed simulator is polynomial time on every
finite bitstring, including malformed protocol inputs and arbitrary raw
source replies. Each call uses its actual request length. The group and
normalization certificates supply their own all-input stopping bounds;
no abstract simulator or external program transformation is assumed. -/
theorem nativeSimulator_polynomialTime (N : RepresentedChooseNormalizer M)
    (source : Program) (q : Nat → Nat) (hPolynomial : PolynomiallyBounded q)
    (hSource : ∀ input, HaltsWithin source input (q input.length)) :
    PolynomialTime (N.simulatorCode source) := by
  obtain ⟨sourceCoefficient, sourceDegree, hSourceBound⟩ :=
    MachineAdversaryInterface.global_monomial_of_polynomiallyBounded hPolynomial
  obtain ⟨normalizationCoefficient, normalizationDegree, hNormalizationBound⟩ :=
    MachineAdversaryInterface.global_monomial_of_polynomiallyBounded N.budget_polynomial
  obtain ⟨multiplyCoefficient, multiplyDegree, hMultiplyBound⟩ :=
    MachineAdversaryInterface.global_monomial_of_polynomiallyBounded M.multiplyBudget_polynomial
  exact chooseChallengeGuessCompile_polynomialTime_of_monomials source N.program M.multiplyProgram source
    sourceCoefficient sourceDegree normalizationCoefficient normalizationDegree
    multiplyCoefficient multiplyDegree sourceCoefficient sourceDegree
    (fun request => (hSource request).mono (hSourceBound request.length))
    (fun request => (N.halts request).mono (hNormalizationBound request.length))
    (fun request => (M.multiplyHalts request).mono (hMultiplyBound request.length))
    (fun request => (hSource request).mono (hSourceBound request.length))

end ElGamal.RepresentedChooseNormalizer
