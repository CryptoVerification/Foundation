import Foundation.Constructions.ElGamal.ToDDH
import Foundation.Assumptions.DDH.Concrete
import Foundation.Notions.PKE.ConcreteINDCPA

open Foundation.Probability

namespace ElGamal

/-- Uniform finite sampling is invariant under a bijective relabeling. -/
private theorem uniform_map_equiv {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply]
  have hsingle : (∑' a : α, if b = e a then (PMF.uniformOfFintype α) a else 0) =
      (PMF.uniformOfFintype α) (e.symm b) := by
    rw [tsum_eq_single (e.symm b)]
    · simp
    · intro a ha
      simp only [ite_eq_right_iff]
      intro h
      exact False.elim (ha (by simpa using congrArg e.symm h.symm))
  rw [hsingle]
  simp [Fintype.card_congr e]

/-- The finite algebra and permutation facts needed for the concrete game
proof. They are external to the syntax-only `DDHParameters`. `powerEquiv`
says that sampling a uniform scalar yields a uniform group element;
`mulLeftEquiv` says multiplication by a fixed message permutes elements. -/
structure FiniteAlgebra (params : DDHParameters) where
  sampling : DDHFiniteSampling params
  powerEquiv : params.Scalar ≃ params.Element
  powerEquiv_apply : ∀ x, powerEquiv x = params.power params.generator x
  mulLeftEquiv : params.Element → params.Element ≃ params.Element
  mulLeftEquiv_apply : ∀ m t, mulLeftEquiv m t = params.mul m t
  power_mul : ∀ x y,
    params.power (params.power params.generator x) y =
      params.power params.generator (params.mulScalar x y)

set_option linter.style.haveILetI false in
/-- Multiplying a uniform DDH mask by any fixed message preserves its
distribution. The proof uses the two explicit finite permutations; it does
not assume challenge-bit independence. -/
theorem randomMask_distribution (params : DDHParameters) (L : FiniteAlgebra params)
    (m : params.Element) :
    (L.sampling.sampleScalar).map
      (fun z => params.mul m (params.power params.generator z)) =
    (L.sampling.sampleScalar).map
      (fun z => params.power params.generator z) := by
  classical
  letI := L.sampling.scalarFintype
  letI := L.sampling.scalarNonempty
  letI : Fintype params.Element := Fintype.ofEquiv params.Scalar L.powerEquiv
  letI : Nonempty params.Element := ⟨L.powerEquiv (Classical.choice L.sampling.scalarNonempty)⟩
  have hleft := uniform_map_equiv (L.powerEquiv.trans (L.mulLeftEquiv m))
  have hright := uniform_map_equiv L.powerEquiv
  change (PMF.uniformOfFintype params.Scalar).map
      (fun z => params.mul m (params.power params.generator z)) =
    (PMF.uniformOfFintype params.Scalar).map
      (fun z => params.power params.generator z)
  calc
    _ = (PMF.uniformOfFintype params.Scalar).map
        (L.powerEquiv.trans (L.mulLeftEquiv m)) := by
          congr 1
          funext z
          simp [L.powerEquiv_apply, L.mulLeftEquiv_apply]
    _ = PMF.uniformOfFintype params.Element := hleft
    _ = (PMF.uniformOfFintype params.Scalar).map L.powerEquiv := hright.symm
    _ = _ := by
      congr 1
      funext z
      exact L.powerEquiv_apply z

/-- The permutation equality remains valid after any probabilistic
continuation, including an adversary's randomized guess. -/
theorem randomMask_bind (params : DDHParameters) (L : FiniteAlgebra params)
    (m : params.Element) {α : Type*} (K : params.Element → PMF α) :
    (L.sampling.sampleScalar).bind
      (fun z => K (params.mul m (params.power params.generator z))) =
    (L.sampling.sampleScalar).bind
      (fun z => K (params.power params.generator z)) := by
  have h := congrArg (fun p : PMF params.Element => p.bind K)
    (randomMask_distribution params L m)
  simpa only [PMF.bind_map, Function.comp_def] using h

private theorem fairBit_match_fixed (guess : Bool) :
    sampleBit.bind (fun β => PMF.pure (guess == β)) = sampleBit := by
  ext b
  simp [PMF.bind_apply, sampleBit, uniform, tsum_fintype]
  cases guess <;> cases b <;> norm_num

/-- An independent guess produces a fair success bit. -/
theorem independentGuess_game_eq (K : PMF Bool) :
    (sampleBit.bind fun β => K.bind fun guess => PMF.pure (guess == β)) =
      sampleBit := by
  rw [PMF.bind_comm sampleBit K (fun β guess => PMF.pure (guess == β))]
  simp_rw [fairBit_match_fixed]
  exact PMF.bind_const K sampleBit

/-- A guess sampled independently of the fair challenge bit succeeds with
probability one half, regardless of the guess distribution. -/
theorem independentGuess_success (K : PMF Bool) :
    eventProb
      (sampleBit.bind fun β => K.bind fun guess => PMF.pure (guess == β))
      (· = true) = 1 / 2 := by
  rw [independentGuess_game_eq]
  simp [eventProb, sampleBit, uniform]

/-- Expose the existing simulator's PMF bind order for distribution proofs. -/
theorem simulator_distinguish_eq (I : ElGamalInstance ProbComp)
    (A : INDCPAAdversary ProbComp I.scheme)
    (X Y T : I.params.Element) :
    (ddhAdversaryOfINDCPA sampleBit I A).distinguish X Y T =
      (A.choose X).bind fun (m₀, m₁, state) =>
        sampleBit.bind fun β =>
          (A.guess state
            (challengeCiphertext I.params (if β then m₁ else m₀) Y T)).bind fun guess =>
              PMF.pure (guess == β) := by
  rfl

/-- Probabilistic ElGamal operations induced by the DDH parameter algebra.
The decryptor is external and is irrelevant to the IND-CPA experiment. -/
noncomputable def concreteConstruction (params : DDHParameters)
    (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element) :
    ElGamalConstruction ProbComp params where
  keygen := (L.sampling.sampleScalar).map fun x => (params.power params.generator x, x)
  encrypt pk m := (L.sampling.sampleScalar).map fun r =>
    (params.power params.generator r, params.mul m (params.power pk r))
  decrypt := decrypt

noncomputable def concreteInstance (params : DDHParameters)
    (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element) :
    ElGamalInstance ProbComp where
  params := params
  construction := concreteConstruction params L decrypt

/-- A real DDH triple gives exactly the ciphertext produced with public-key
exponent `x` and encryption randomness `y`. -/
theorem realTuple_challengeCiphertext_eq_encryption (params : DDHParameters)
    (L : FiniteAlgebra params) (m : params.Element) (x y : params.Scalar) :
    challengeCiphertext params m
      (params.power params.generator y)
      (params.power params.generator (params.mulScalar x y)) =
    (params.power params.generator y,
      params.mul m (params.power (params.power params.generator x) y)) := by
  simp [challengeCiphertext, L.power_mul]

private theorem bind_three_comm {α β γ δ : Type*}
    (p : PMF α) (q : PMF β) (r : PMF γ)
    (f : α → β → γ → PMF δ) :
    p.bind (fun a => q.bind (fun b => r.bind (fun c => f a b c))) =
    q.bind (fun b => r.bind (fun c => p.bind (fun a => f a b c))) := by
  rw [PMF.bind_comm p q]
  congr 1
  funext b
  exact PMF.bind_comm p r (fun a c => f a b c)

private noncomputable def realGameNormal (params : DDHParameters)
    (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element)
    (A : INDCPAAdversary ProbComp (concreteInstance params L decrypt).scheme) :
    PMF Bool :=
  L.sampling.sampleScalar.bind fun x =>
    (A.choose (params.power params.generator x)).bind fun (m₀, m₁, state) =>
      sampleBit.bind fun β =>
        L.sampling.sampleScalar.bind fun y =>
          (A.guess state
            (challengeCiphertext params (if β then m₁ else m₀)
              (params.power params.generator y)
              (params.power params.generator (params.mulScalar x y)))).bind fun guess =>
                PMF.pure (guess == β)

private noncomputable def randomGameNormal (params : DDHParameters)
    (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element)
    (A : INDCPAAdversary ProbComp (concreteInstance params L decrypt).scheme) :
    PMF Bool :=
  L.sampling.sampleScalar.bind fun x =>
    L.sampling.sampleScalar.bind fun y =>
      (A.choose (params.power params.generator x)).bind fun (m₀, m₁, state) =>
        sampleBit.bind fun β =>
          L.sampling.sampleScalar.bind fun z =>
            (A.guess state
              (challengeCiphertext params (if β then m₁ else m₀)
                (params.power params.generator y)
                (params.power params.generator z))).bind fun guess =>
                  PMF.pure (guess == β)

private noncomputable def randomGameUnmasked (params : DDHParameters)
    (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element)
    (A : INDCPAAdversary ProbComp (concreteInstance params L decrypt).scheme) :
    PMF Bool :=
  L.sampling.sampleScalar.bind fun x =>
    L.sampling.sampleScalar.bind fun y =>
      (A.choose (params.power params.generator x)).bind fun (_m₀, _m₁, state) =>
        sampleBit.bind fun β =>
          L.sampling.sampleScalar.bind fun z =>
            (A.guess state
              (params.power params.generator y, params.power params.generator z)).bind
                fun guess => PMF.pure (guess == β)

theorem randomGame_mask_independent (params : DDHParameters) (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element)
    (A : INDCPAAdversary ProbComp (concreteInstance params L decrypt).scheme) :
    randomGameNormal params L decrypt A =
    randomGameUnmasked params L decrypt A := by
  unfold randomGameNormal randomGameUnmasked
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext messages
  rcases messages with ⟨m₀, m₁, state⟩
  dsimp
  congr 1
  funext β
  change (L.sampling.sampleScalar).bind
      (fun z => (A.guess state
        (params.power params.generator y,
          params.mul (if β then m₁ else m₀) (params.power params.generator z))).bind
        fun guess => PMF.pure (guess == β)) =
    (L.sampling.sampleScalar).bind
      (fun z => (A.guess state
        (params.power params.generator y, params.power params.generator z)).bind
        fun guess => PMF.pure (guess == β))
  exact randomMask_bind params L (if β then m₁ else m₀)
      (fun T => (A.guess state (params.power params.generator y, T)).bind
        fun guess => PMF.pure (guess == β))

/-- After removing the message mask, the transcript is independent of the
challenge bit, so the success bit itself is fair. -/
theorem randomGameUnmasked_eq_sampleBit (params : DDHParameters)
    (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element)
    (A : INDCPAAdversary ProbComp (concreteInstance params L decrypt).scheme) :
    randomGameUnmasked params L decrypt A = sampleBit := by
  unfold randomGameUnmasked
  simp_rw [← PMF.bind_bind]
  simp_rw [independentGuess_game_eq]
  simp

theorem randomBranch_game_eq_normal (params : DDHParameters) (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element)
    (A : INDCPAAdversary ProbComp (concreteInstance params L decrypt).scheme) :
    ddhRandomGame params L.sampling
      (ddhAdversaryOfINDCPA sampleBit (concreteInstance params L decrypt) A) =
    randomGameNormal params L decrypt A := by
  unfold ddhRandomGame randomGameNormal
  congr 1
  funext x
  congr 1
  funext y
  calc
    _ = L.sampling.sampleScalar.bind (fun z =>
        (A.choose (params.power params.generator x)).bind fun (m₀, m₁, state) =>
          sampleBit.bind fun β =>
            (A.guess state
              (challengeCiphertext params (if β then m₁ else m₀)
                (params.power params.generator y)
                (params.power params.generator z))).bind fun guess =>
                  PMF.pure (guess == β)) := by rfl
    _ = _ := by
      exact bind_three_comm L.sampling.sampleScalar
        (A.choose (params.power params.generator x)) sampleBit
        (fun z (m₀, m₁, state) β =>
          (A.guess state
            (challengeCiphertext params (if β then m₁ else m₀)
              (params.power params.generator y)
              (params.power params.generator z))).bind fun guess =>
                PMF.pure (guess == β))

theorem randomBranch_game_eq_sampleBit (params : DDHParameters) (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element)
    (A : INDCPAAdversary ProbComp (concreteInstance params L decrypt).scheme) :
    ddhRandomGame params L.sampling
      (ddhAdversaryOfINDCPA sampleBit (concreteInstance params L decrypt) A) =
    sampleBit := by
  calc
    _ = randomGameNormal params L decrypt A :=
      randomBranch_game_eq_normal params L decrypt A
    _ = randomGameUnmasked params L decrypt A :=
      randomGame_mask_independent params L decrypt A
    _ = sampleBit := randomGameUnmasked_eq_sampleBit params L decrypt A

/-- The real DDH branch of the existing simulator has the same output
distribution as the concrete left-or-right IND-CPA experiment. -/
theorem realBranch_game_eq (params : DDHParameters) (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element)
    (A : INDCPAAdversary ProbComp (concreteInstance params L decrypt).scheme) :
    ddhRealGame params L.sampling
      (ddhAdversaryOfINDCPA sampleBit (concreteInstance params L decrypt) A) =
    indCPAExperiment (concreteInstance params L decrypt).scheme A := by
  calc
    _ = realGameNormal params L decrypt A := by
      unfold ddhRealGame realGameNormal
      congr 1
      funext x
      calc
        _ = L.sampling.sampleScalar.bind (fun y =>
            (A.choose (params.power params.generator x)).bind fun (m₀, m₁, state) =>
              sampleBit.bind fun β =>
                (A.guess state
                  (challengeCiphertext params (if β then m₁ else m₀)
                    (params.power params.generator y)
                    (params.power params.generator (params.mulScalar x y)))).bind fun guess =>
                    PMF.pure (guess == β)) := by
          rfl
        _ = _ := by
          exact bind_three_comm L.sampling.sampleScalar
            (A.choose (params.power params.generator x)) sampleBit
            (fun y (m₀, m₁, state) β =>
              (A.guess state
                (challengeCiphertext params (if β then m₁ else m₀)
                  (params.power params.generator y)
                  (params.power params.generator (params.mulScalar x y)))).bind fun guess =>
                    PMF.pure (guess == β))
    _ = _ := by
      simp [realGameNormal, indCPAExperiment, concreteInstance,
        concreteConstruction, ElGamalInstance.scheme, ElGamalConstruction.scheme,
        PMF.bind_map, Function.comp_def, challengeCiphertext, L.power_mul]

/-- For the actual finite ElGamal construction, the existing simulator has
exactly the IND-CPA advantage under the Phase 11a probability-gap convention. -/
theorem concrete_advantage_eq (params : DDHParameters) (L : FiniteAlgebra params)
    (decrypt : params.Scalar → (params.Element × params.Element) → Option params.Element)
    (A : INDCPAAdversary ProbComp (concreteInstance params L decrypt).scheme) :
    ddhAdvantage params L.sampling
      (ddhAdversaryOfINDCPA sampleBit (concreteInstance params L decrypt) A) =
    indCPAAdvantage (concreteInstance params L decrypt).scheme A := by
  unfold ddhAdvantage indCPAAdvantage indCPASuccessProb guessingAdvantage
  rw [realBranch_game_eq, randomBranch_game_eq_sampleBit]
  simp [eventProb, sampleBit, uniform]

end ElGamal
