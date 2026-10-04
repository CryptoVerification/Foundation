import Foundation.Machine.CryptoInterfaces
import Foundation.Machine.ProgramTransformation
import Foundation.Notions.PKE.ConcreteINDCPA

open Foundation.Probability

/-- The IND-CPA game calls `guess` only on states in the support of a
preceding `choose` call. Changing `guess` elsewhere leaves the full PMF
experiment unchanged. This is the semantic basis for bounding reachable
requests instead of every possible bitstring state. -/
theorem indCPAExperiment_guess_congr_on_choose_support
    (scheme : PKE ProbComp)
    (A : INDCPAAdversary ProbComp scheme)
    (guess' : A.State → scheme.Ciphertext → ProbComp Bool)
    (h : ∀ (pk : scheme.PublicKey)
      (messages : scheme.Message × scheme.Message × A.State),
      messages ∈ (A.choose pk).support →
      ∀ ciphertext, A.guess messages.2.2 ciphertext =
        guess' messages.2.2 ciphertext) :
    indCPAExperiment scheme A =
      indCPAExperiment scheme
        { State := A.State, choose := A.choose, guess := guess' } := by
  unfold indCPAExperiment
  congr 1
  funext keys
  rcases keys with ⟨pk, sk⟩
  dsimp only
  rw [← PMF.bindOnSupport_eq_bind (A.choose pk),
    ← PMF.bindOnSupport_eq_bind (A.choose pk)]
  congr 1
  funext messages hmessages
  rcases messages with ⟨m₀, m₁, state⟩
  congr 1
  funext bit
  congr 1
  funext ciphertext
  rw [h pk (m₀, m₁, state) hmessages ciphertext]

theorem indCPAAdvantage_guess_congr_on_choose_support
    (scheme : PKE ProbComp)
    (A : INDCPAAdversary ProbComp scheme)
    (guess' : A.State → scheme.Ciphertext → ProbComp Bool)
    (h : ∀ (pk : scheme.PublicKey)
      (messages : scheme.Message × scheme.Message × A.State),
      messages ∈ (A.choose pk).support →
      ∀ ciphertext, A.guess messages.2.2 ciphertext =
        guess' messages.2.2 ciphertext) :
    indCPAAdvantage scheme A =
      indCPAAdvantage scheme
        { State := A.State, choose := A.choose, guess := guess' } := by
  unfold indCPAAdvantage indCPASuccessProb
  rw [indCPAExperiment_guess_congr_on_choose_support scheme A guess' h]

/-- A bound on the state actually returned by `choose` is sufficient for
replacing `guess` outside that bound. No global bound on all `List Bool`
states is required by the IND-CPA experiment. -/
theorem indCPAAdvantage_guess_congr_of_reachable_state_bound
    (scheme : PKE ProbComp)
    (A : INDCPAAdversary ProbComp scheme)
    (stateSize : A.State → Nat)
    (guess' : A.State → scheme.Ciphertext → ProbComp Bool)
    (limit : Nat)
    (hBound : ∀ (pk : scheme.PublicKey)
      (messages : scheme.Message × scheme.Message × A.State),
      messages ∈ (A.choose pk).support →
      stateSize messages.2.2 ≤ limit)
    (hGuess : ∀ state : A.State,
      stateSize state ≤ limit →
      ∀ ciphertext, A.guess state ciphertext = guess' state ciphertext) :
    indCPAAdvantage scheme A =
      indCPAAdvantage scheme
        { State := A.State, choose := A.choose, guess := guess' } := by
  apply indCPAAdvantage_guess_congr_on_choose_support scheme A guess'
  intro pk messages hmessages ciphertext
  exact hGuess messages.2.2 (hBound pk messages hmessages) ciphertext

namespace Machine

universe v a b

/-- A choose response decoder is state-size faithful if it cannot expand a
short machine output code into a long adversary state. This is an explicit
computational-representation requirement, independent of round-trip coding. -/
def ChooseStateSizeFaithful
    (X : Nat → Type 1) (scheme : ∀ n, X n → PKE ProbComp)
    (responseCode : ∀ n (x : X n),
      FiniteBitEncoding (((scheme n x).Message ×
        (scheme n x).Message × List Bool) ⊕ Bool)) : Prop :=
  ∀ n (x : X n) bits m₀ m₁ state,
    (responseCode n x).decode bits = some (.inl (m₀, m₁, state)) →
      state.length ≤ bits.length

/-- The only states observed by the IND-CPA game come from choose responses.
For a size-faithful decoder, their length is bounded by the actual step
budget of the choose invocation. Arbitrary states supplied directly to
`guess` remain unbounded, as shown by `indCPAReindexedInterface_pptClass_empty`. -/
theorem indCPAReindexed_choose_state_length_le
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
    (hFaithful : ChooseStateSizeFaithful X scheme responseCode)
    (p : Program) (budget : Nat → Nat)
    (n : Nat) (x : X n) (pk : (scheme n x).PublicKey)
    (messages : (scheme n x).Message × (scheme n x).Message × List Bool)
    (hMessages : messages ∈
      (((indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).responseWithin p budget n x (.inl pk)).map
        (fun answer => match answer with
          | .inl messages => messages
          | .inr _ => (defaultMessage n x, defaultMessage n x, []))).support) :
    messages.2.2.length ≤
      budget ((indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).machineInput n x (.inl pk)).length + 1 := by
  let J := indCPAReindexedInterface S X scheme instanceCode
    requestCode responseCode defaultMessage
  rw [PMF.mem_support_map_iff] at hMessages
  rcases hMessages with ⟨answer, hAnswer, hEq⟩
  cases answer with
  | inr bit =>
      simp at hEq
      cases hEq
      simp
  | inl triple =>
      rcases triple with ⟨m₀, m₁, state⟩
      have hDecoder : ∀ bits answer,
          (J.responseEncoding n x).decode bits = some answer →
            (match answer with
              | .inl (_, _, state) => state.length
              | .inr _ => 0) ≤ bits.length := by
        intro bits answer hDecode
        cases answer with
        | inr bit => simp
        | inl value =>
            rcases value with ⟨m₀, m₁, state⟩
            exact hFaithful n x bits m₀ m₁ state hDecode
      have hSize := J.responseWithin_size_le_of_mem_support p budget n x
        (.inl pk)
        (fun answer => match answer with
          | .inl (_, _, state) => state.length
          | .inr _ => 0)
        hDecoder (.inl (m₀, m₁, state)) hAnswer (by simp [J, indCPAReindexedInterface])
      simp at hEq
      cases hEq
      exact hSize

/-- A polynomial bound on the choose request size and a polynomial machine
budget yield a polynomial bound on states that choose can actually produce.
This avoids the impossible all-state input bound. -/
theorem indCPAReindexed_reachable_state_polynomial
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
    (hFaithful : ChooseStateSizeFaithful X scheme responseCode)
    (F : (n : Nat) → X n)
    (p : Program) (budget : Nat → Nat)
    (hBudget : PolynomiallyBounded budget)
    (size : Nat → Nat) (hSize : PolynomiallyBounded size)
    (hChooseSize : ∀ n (pk : (scheme n (F n)).PublicKey),
      ((indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).machineInput n (F n) (.inl pk)).length ≤
        size n) :
    ∃ stateBound : Nat → Nat, PolynomiallyBounded stateBound ∧
      ∀ n (pk : (scheme n (F n)).PublicKey)
        (messages : (scheme n (F n)).Message ×
          (scheme n (F n)).Message × List Bool),
        messages ∈
          (((indCPAReindexedInterface S X scheme instanceCode requestCode
            responseCode defaultMessage).responseWithin p budget n (F n) (.inl pk)).map
            (fun answer => match answer with
              | .inl messages => messages
              | .inr _ => (defaultMessage n (F n), defaultMessage n (F n), []))).support →
        messages.2.2.length ≤ stateBound n := by
  obtain ⟨c, k, hGlobal⟩ :=
    MachineAdversaryInterface.global_monomial_of_polynomiallyBounded hBudget
  let stateBound : Nat → Nat := fun n => c * (size n + 1) ^ k + 1
  have hStatePoly : PolynomiallyBounded stateBound := by
    exact ((PolynomiallyBounded.const c).mul
      ((hSize.add (PolynomiallyBounded.const 1)).pow k)).add
        (PolynomiallyBounded.const 1)
  refine ⟨stateBound, hStatePoly, ?_⟩
  intro n pk messages hMessages
  have hMachine : messages.2.2.length ≤
      budget ((indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).machineInput n (F n) (.inl pk)).length + 1 := by
    apply indCPAReindexed_choose_state_length_le
      S X scheme instanceCode requestCode responseCode defaultMessage
      hFaithful p budget n (F n) pk messages
    simpa [indCPAReindexedInterface] using hMessages
  have hInput := hChooseSize n pk
  have hRuntime : budget
      ((indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).machineInput n (F n) (.inl pk)).length + 1 ≤
      stateBound n := by
    dsimp [stateBound]
    have hPow := Nat.pow_le_pow_left
      (Nat.add_le_add_right hInput 1) k
    have hBound := hGlobal
      ((indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).machineInput n (F n) (.inl pk)).length
    have hMul := Nat.mul_le_mul_left c hPow
    omega
  exact hMachine.trans hRuntime

/-- A polynomial bound for the fixed part of each protocol request, together
with the reachable choose-state bound, gives a common polynomial bound on
machine inputs actually issued by the two-stage IND-CPA experiment. The
guess bound is required only for states returned by `choose`; it does not
assert the impossible all-state `InputSizeBound`. -/
theorem indCPAReindexed_reachable_input_polynomial
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
    (hFaithful : ChooseStateSizeFaithful X scheme responseCode)
    (F : (n : Nat) → X n)
    (p : Program) (budget : Nat → Nat)
    (hBudget : PolynomiallyBounded budget)
    (size : Nat → Nat) (hSize : PolynomiallyBounded size)
    (hChooseSize : ∀ n (pk : (scheme n (F n)).PublicKey),
      ((indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).machineInput n (F n) (.inl pk)).length ≤
        size n)
    (hGuessSize : ∀ n (state : List Bool)
        (ciphertext : (scheme n (F n)).Ciphertext),
      ((indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).machineInput n (F n)
          (.inr (state, ciphertext))).length ≤
        size n * (state.length + 1)) :
    ∃ inputBound : Nat → Nat, PolynomiallyBounded inputBound ∧
      (∀ n (pk : (scheme n (F n)).PublicKey),
        ((indCPAReindexedInterface S X scheme instanceCode requestCode
          responseCode defaultMessage).machineInput n (F n) (.inl pk)).length ≤
          inputBound n) ∧
      (∀ n (pk : (scheme n (F n)).PublicKey)
        (messages : (scheme n (F n)).Message ×
          (scheme n (F n)).Message × List Bool),
        messages ∈
          (((indCPAReindexedInterface S X scheme instanceCode requestCode
            responseCode defaultMessage).responseWithin p budget n (F n) (.inl pk)).map
            (fun answer => match answer with
              | .inl messages => messages
              | .inr _ => (defaultMessage n (F n), defaultMessage n (F n), []))).support →
        ∀ ciphertext : (scheme n (F n)).Ciphertext,
          ((indCPAReindexedInterface S X scheme instanceCode requestCode
            responseCode defaultMessage).machineInput n (F n)
              (.inr (messages.2.2, ciphertext))).length ≤ inputBound n) := by
  obtain ⟨stateBound, hStatePoly, hState⟩ :=
    indCPAReindexed_reachable_state_polynomial S X scheme instanceCode
      requestCode responseCode defaultMessage hFaithful F p budget hBudget
      size hSize hChooseSize
  let inputBound := fun n => size n * (stateBound n + 1)
  refine ⟨inputBound,
    hSize.mul (hStatePoly.add (PolynomiallyBounded.const 1)), ?_, ?_⟩
  · intro n pk
    have h := hChooseSize n pk
    exact h.trans (by
      dsimp [inputBound]
      exact Nat.le_mul_of_pos_right (size n) (by omega))
  · intro n pk messages hMessages ciphertext
    have hStateLength : messages.2.2.length ≤ stateBound n := by
      apply hState n pk messages
      simpa [indCPAReindexedInterface] using hMessages
    have hInput := hGuessSize n messages.2.2 ciphertext
    dsimp [inputBound]
    exact hInput.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hStateLength 1))

/-- Machine adversaries for the two-stage IND-CPA protocol, with a polynomial
input-size discipline that accounts for the state only when it is returned
by `choose`. The fixed machine code and worst-case runtime condition are the
same as in `MachineAdversaryInterface.pptClass`. The stage-specific size laws
are explicit encoding assumptions; this definition does not derive them from
finite encodability alone. The `hFaithful` argument certifies that decoding a
choose response cannot expand its state beyond the emitted machine bits. -/
noncomputable def indCPAReindexedReachablePPTClass
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
    (_hFaithful : ChooseStateSizeFaithful X scheme responseCode) :
    AdversaryClass ((INDCPA ProbComp S).reindex X scheme) where
  admissible F A :=
    ∃ (p : Program) (budget size : Nat → Nat),
      PolynomiallyBounded budget ∧
      (∀ input : List Bool,
        HaltsWithin p input (budget input.length)) ∧
      PolynomiallyBounded size ∧
      (∀ n (pk : (scheme n (F n)).PublicKey),
        ((indCPAReindexedInterface S X scheme instanceCode requestCode
          responseCode defaultMessage).machineInput n (F n) (.inl pk)).length ≤
            size n) ∧
      (∀ n (state : List Bool)
        (ciphertext : (scheme n (F n)).Ciphertext),
        ((indCPAReindexedInterface S X scheme instanceCode requestCode
          responseCode defaultMessage).machineInput n (F n)
            (.inr (state, ciphertext))).length ≤
          size n * (state.length + 1)) ∧
      (indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).Realizes F p budget A

/-- An admissible adversary in the reachable-request class has a common
polynomial input bound on every request actually made by its IND-CPA game.
This conclusion requires a decoder that does not expand a short output code
into a longer state. -/
theorem indCPAReindexedReachablePPTClass_input_polynomial
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
    (hFaithful : ChooseStateSizeFaithful X scheme responseCode)
    (F : (n : Nat) → X n)
    (A : AdversaryFamily ((INDCPA ProbComp S).reindex X scheme) F)
    (hA : (indCPAReindexedReachablePPTClass S X scheme instanceCode
      requestCode responseCode defaultMessage hFaithful).admissible F A) :
    ∃ (p : Program) (budget inputBound : Nat → Nat),
      PolynomiallyBounded inputBound ∧
      (∀ n (pk : (scheme n (F n)).PublicKey),
        ((indCPAReindexedInterface S X scheme instanceCode requestCode
          responseCode defaultMessage).machineInput n (F n) (.inl pk)).length ≤
          inputBound n) ∧
      (∀ n (pk : (scheme n (F n)).PublicKey)
        (messages : (scheme n (F n)).Message ×
          (scheme n (F n)).Message × List Bool),
        messages ∈
          (((indCPAReindexedInterface S X scheme instanceCode requestCode
            responseCode defaultMessage).responseWithin p budget n (F n) (.inl pk)).map
            (fun answer => match answer with
              | .inl messages => messages
              | .inr _ => (defaultMessage n (F n), defaultMessage n (F n), []))).support →
        ∀ ciphertext : (scheme n (F n)).Ciphertext,
          ((indCPAReindexedInterface S X scheme instanceCode requestCode
            responseCode defaultMessage).machineInput n (F n)
              (.inr (messages.2.2, ciphertext))).length ≤ inputBound n) ∧
      (indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).Realizes F p budget A := by
  rcases hA with ⟨p, budget, size, hBudget, _, hSize,
    hChooseSize, hGuessSize, hRealizes⟩
  obtain ⟨inputBound, hInputPoly, hChoose, hGuess⟩ :=
    indCPAReindexed_reachable_input_polynomial S X scheme instanceCode
      requestCode responseCode defaultMessage hFaithful F p budget hBudget
      size hSize hChooseSize hGuessSize
  exact ⟨p, budget, inputBound, hInputPoly, hChoose, hGuess, hRealizes⟩

/-- The same machine code halts within a polynomial in the security parameter
on the choose call and on guess calls reached from that choose call. The
bound is not asserted for arbitrary caller-supplied states. -/
theorem indCPAReindexedReachablePPTClass_haltsWithin_securityPolynomial
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
    (hFaithful : ChooseStateSizeFaithful X scheme responseCode)
    (F : (n : Nat) → X n)
    (A : AdversaryFamily ((INDCPA ProbComp S).reindex X scheme) F)
    (hA : (indCPAReindexedReachablePPTClass S X scheme instanceCode
      requestCode responseCode defaultMessage hFaithful).admissible F A) :
    ∃ (p : Program) (budget runBound : Nat → Nat),
      PolynomiallyBounded runBound ∧
      (∀ n (pk : (scheme n (F n)).PublicKey),
        HaltsWithin p
          ((indCPAReindexedInterface S X scheme instanceCode requestCode
            responseCode defaultMessage).machineInput n (F n) (.inl pk))
          (runBound n)) ∧
      (∀ n (pk : (scheme n (F n)).PublicKey)
        (messages : (scheme n (F n)).Message ×
          (scheme n (F n)).Message × List Bool),
        messages ∈
          (((indCPAReindexedInterface S X scheme instanceCode requestCode
            responseCode defaultMessage).responseWithin p budget n (F n) (.inl pk)).map
            (fun answer => match answer with
              | .inl messages => messages
              | .inr _ => (defaultMessage n (F n), defaultMessage n (F n), []))).support →
        ∀ ciphertext : (scheme n (F n)).Ciphertext,
          HaltsWithin p
            ((indCPAReindexedInterface S X scheme instanceCode requestCode
              responseCode defaultMessage).machineInput n (F n)
                (.inr (messages.2.2, ciphertext))) (runBound n)) ∧
      (indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage).Realizes F p budget A := by
  rcases hA with ⟨p, budget, size, hBudget, hHalts, hSize,
    hChooseSize, hGuessSize, hRealizes⟩
  obtain ⟨inputBound, hInputPoly, hChoose, hGuess⟩ :=
    indCPAReindexed_reachable_input_polynomial S X scheme instanceCode
      requestCode responseCode defaultMessage hFaithful F p budget hBudget
      size hSize hChooseSize hGuessSize
  obtain ⟨c, k, hGlobal⟩ :=
    MachineAdversaryInterface.global_monomial_of_polynomiallyBounded hBudget
  let runBound : Nat → Nat := fun n => c * (inputBound n + 1)^k
  have hRunPoly : PolynomiallyBounded runBound := by
    exact (PolynomiallyBounded.const c).mul
      ((hInputPoly.add (PolynomiallyBounded.const 1)).pow k)
  have hRun (n : Nat) (input : List Bool)
      (hLength : input.length ≤ inputBound n) :
      HaltsWithin p input (runBound n) := by
    have hBudgetLe : budget input.length ≤ runBound n := by
      exact (hGlobal input.length).trans
        (Nat.mul_le_mul_left c
          (Nat.pow_le_pow_left (Nat.add_le_add_right hLength 1) k))
    exact (hHalts input).mono hBudgetLe
  refine ⟨p, budget, runBound, hRunPoly, ?_, ?_, hRealizes⟩
  · intro n pk
    exact hRun n _ (hChoose n pk)
  · intro n pk messages hMessages ciphertext
    have hLength := hGuess n pk messages (by
      simpa [indCPAReindexedInterface] using hMessages) ciphertext
    exact hRun n _ hLength

/-- A finite-code compiler certificate transports the reachable IND-CPA
machine class to a target machine-PPT class when target protocol inputs have
an independent polynomial size bound. `MachineProgramSimulation` carries no
all-request source `InputSizeBound`, which cannot exist for this adapter.
This theorem does not construct a compiler or target size witness. -/
theorem indCPAReindexedReachablePPTClass_preserved
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
    (hFaithful : ChooseStateSizeFaithful X scheme responseCode)
    {Q : CryptoGoal.{v}}
    (R : Reduction ((INDCPA ProbComp S).reindex X scheme) Q)
    (JQ : MachineAdversaryInterface.{v, a, b} Q)
    (T : R.MachineProgramSimulation
      (indCPAReindexedInterface S X scheme instanceCode requestCode
        responseCode defaultMessage) JQ)
    (hTargetSize : ∀ F : InstanceFamily ((INDCPA ProbComp S).reindex X scheme),
      ∃ size : JQ.InputSizeBound (R.mapFamily F),
        PolynomiallyBounded size.limit) :
    R.PreservesAdmissibility
      (indCPAReindexedReachablePPTClass S X scheme instanceCode requestCode
        responseCode defaultMessage hFaithful) JQ.pptClass := by
  constructor
  intro F A hA
  rcases hA with ⟨p, budget, _, hBudget, hHalts, _, _, _, hRealizes⟩
  obtain ⟨targetSize, hTargetPoly⟩ := hTargetSize F
  exact ⟨T.transform p, T.transformBudget budget, targetSize,
    T.budget_polynomiallyBounded hBudget, T.halts p budget hHalts,
    hTargetPoly, T.realizes F A p budget hHalts hRealizes⟩

end Machine
