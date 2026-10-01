import Foundation.Machine.ChooseChallengeCompletion

namespace Machine.GuardedCompiler

/-- A numerical majorant for one complete continuation. Payload sizes and
source storage are charged explicitly; every time function is evaluated at
the actual request length of its own invocation. This bound does not assume
that those functions are monotone. It will support a common polynomial
envelope over choose branches once their sizes and times are bounded. -/
theorem chooseChallengeBranchBudget_bound
    (qNormalize qMultiply qGuess : Nat → Nat) (chooseRequest : List Bool)
    (n : Nat) (instanceBits first second last : List Bool)
    (message₀ message₁ state : Configuration → List Bool)
    (product : Configuration → Bool → List Bool) (c : Configuration) :
    let reply := c.outputBits
    let normalRequest := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
    let selected := fun bit : Bool => if bit then message₁ c else message₀ c
    let multiplyRequest := fun bit => encodeSecurityParameter n ++ frame instanceBits ++ frame (selected bit) ++ frame last
    let guessRequest := fun bit => guessFromProductRequest n instanceBits second (state c) (product c bit)
    let size := n + instanceBits.length + first.length + second.length + last.length +
      chooseRequest.length + reply.length + (message₀ c).length + (message₁ c).length + (state c).length +
      (product c false).length + (product c true).length + sourceStorage c + 1
    let normalizeTime := qNormalize normalRequest.length
    let time := normalizeTime + qMultiply (multiplyRequest false).length + qMultiply (multiplyRequest true).length +
      qGuess (guessRequest false).length + qGuess (guessRequest true).length + 1
    chooseChallengeBranchBudget qNormalize qMultiply qGuess chooseRequest n instanceBits first second last
      message₀ message₁ state product c ≤ 1300000 * (size + normalizeTime) * time^2 := by
  dsimp only
  let reply := c.outputBits
  let normalRequest := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let selected := fun bit : Bool => if bit then message₁ c else message₀ c
  let multiplyRequest := fun bit => encodeSecurityParameter n ++ frame instanceBits ++ frame (selected bit) ++ frame last
  let guessRequest := fun bit => guessFromProductRequest n instanceBits second (state c) (product c bit)
  let size := n + instanceBits.length + first.length + second.length + last.length +
    chooseRequest.length + reply.length + (message₀ c).length + (message₁ c).length + (state c).length +
    (product c false).length + (product c true).length + sourceStorage c + 1
  let normalizeTime := qNormalize normalRequest.length
  let weight := size + normalizeTime
  let tailTime := qMultiply (multiplyRequest false).length + qMultiply (multiplyRequest true).length +
    qGuess (guessRequest false).length + qGuess (guessRequest true).length + 1
  let time := normalizeTime + qMultiply (multiplyRequest false).length + qMultiply (multiplyRequest true).length +
    qGuess (guessRequest false).length + qGuess (guessRequest true).length + 1
  let branchSize := fun bit => n + instanceBits.length + first.length + second.length + last.length + reply.length +
    (message₀ c).length + (message₁ c).length + (state c).length + (selected bit).length + (product c bit).length +
    (multiplyRequest bit).length + (guessRequest bit).length + chooseRequest.length + normalRequest.length +
    sourceStorage c + (2 * normalRequest.length + 2 + normalizeTime) + 1
  have hPositive : 1 ≤ size := by dsimp only [size]; omega
  have hWeight : size ≤ weight := Nat.le_add_right _ _
  have hTime : 1 ≤ time := by dsimp only [time]; omega
  have hNormTime : normalizeTime + 1 ≤ time := by dsimp only [time]; omega
  have hTailTime : tailTime ≤ time := by dsimp only [tailTime, time]; omega
  have hSquare : 1 ≤ time ^ 2 := Nat.one_le_pow _ _ hTime
  have hMultiplyLen (bit : Bool) : (multiplyRequest bit).length ≤ 5 * size := by
    cases bit <;> simp only [multiplyRequest, selected, Bool.false_eq_true, ↓reduceIte,
      encodeSecurityParameter, frame, List.length_append, List.length_cons, List.length_replicate] <;>
      simp only [List.length_nil] <;>
      dsimp only [size] <;> omega
  have hGuessLen (bit : Bool) : (guessRequest bit).length ≤ 10 * size := by
    cases bit <;> simp only [guessRequest, guessFromProductRequest, encodeSecurityParameter, frame,
      List.length_append, List.length_cons, List.length_replicate, FiniteBitEncoding.delimit_length] <;>
      simp only [List.length_nil] <;>
      dsimp only [size] <;> omega
  have hNormalLen : normalRequest.length ≤ 3 * size := by
    simp only [normalRequest, encodeSecurityParameter, frame, List.length_append,
      List.length_cons, List.length_replicate, List.length_nil]
    dsimp only [size]
    omega
  have hBranchSize (bit : Bool) : branchSize bit ≤ 30 * weight := by
    have hm := hMultiplyLen bit
    have hg := hGuessLen bit
    cases bit <;> dsimp only [branchSize, selected, weight, size] at * <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hPrepare := prepareSelectedMessage_steps_le (message₀ c) (message₁ c) (state c)
  have hPrepareBound : prepareSelectedMessageSteps (message₀ c) (message₁ c) (state c) ≤ 150 * size := by
    simp only [canonicalMessageBits, List.length_cons, List.length_append, FiniteBitEncoding.delimit_length] at hPrepare
    dsimp only [size]
    omega
  have hOriginal : (encodeSecurityParameter n ++ frame instanceBits ++
      frame (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last)).length + reply.length + 1 ≤ 8 * size := by
    simp only [encodeSecurityParameter, frame, List.length_append, List.length_cons,
      List.length_replicate, List.length_nil, FiniteBitEncoding.delimit_length]
    dsimp only [size]
    omega
  have hNorm := normalizationTraceBudget_bound qNormalize n instanceBits
    (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) reply
  have hNormBound : normalizationTraceBudget qNormalize n instanceBits
      (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) reply ≤
        2800 * weight * time ^ 2 := by
    apply hNorm.trans
    change 350 * _ * (normalizeTime + 1)^2 ≤ _
    calc
      _ ≤ 350 * (8 * size) * time^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 350 hOriginal) (Nat.pow_le_pow_left hNormTime 2)
      _ ≤ 350 * (8 * weight) * time^2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 350 (Nat.mul_le_mul_left 8 hWeight))
      _ = _ := by simp only [← Nat.mul_assoc, Nat.reduceMul]
  have hTailBound : 20000 * (branchSize false + branchSize true) * tailTime^2 ≤
      1200000 * weight * time^2 := by
    calc
      _ ≤ 20000 * (60 * weight) * time^2 := by
        have hSize : branchSize false + branchSize true ≤ 60 * weight := by
          simpa only [← Nat.add_mul, Nat.reduceAdd] using
            Nat.add_le_add (hBranchSize false) (hBranchSize true)
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 20000 hSize) (Nat.pow_le_pow_left hTailTime 2)
      _ = _ := by simp only [← Nat.mul_assoc, Nat.reduceMul]
  have hPrepareScaled : prepareSelectedMessageSteps (message₀ c) (message₁ c) (state c) ≤
      150 * weight * time^2 := by
    calc
      _ ≤ 150 * size := hPrepareBound
      _ ≤ 150 * weight := Nat.mul_le_mul_left 150 hWeight
      _ = 150 * weight * 1 := (Nat.mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hSquare
  have hUnit : 1 ≤ weight * time^2 := by
    have hWeightPositive : 1 ≤ weight := hPositive.trans hWeight
    simpa only [Nat.one_mul] using Nat.mul_le_mul hWeightPositive hSquare
  change normalizationTraceBudget qNormalize n instanceBits
    (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last) reply +
      (prepareSelectedMessageSteps (message₀ c) (message₁ c) (state c) +
        (20000 * (branchSize false + branchSize true) * tailTime^2 + 1) + 1) ≤ 1300000 * weight * time^2
  simp only [Nat.mul_assoc] at hNormBound hTailBound hPrepareScaled ⊢
  omega

end Machine.GuardedCompiler
