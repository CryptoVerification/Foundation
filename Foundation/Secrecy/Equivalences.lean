import Foundation.Secrecy.Basic

namespace Secrecy

open SymmetricEncryption
open scoped BigOperators

variable {Key Msg Ciph : Type _}

section
variable [Fintype Key] [DecidableEq Ciph]
variable [Nonempty Key] [Fintype Ciph]

theorem perfectSecrecy_iff_perfectIndistinguishability
    (scheme : SymmetricEncryption Key Msg Ciph) :
    perfectSecrecy scheme ↔ perfectIndistinguishability scheme := by
  classical
  constructor
  · intro h
    have hCount :=
      (perfectSecrecy_iff_card (scheme := scheme)).1 h
    refine
      (perfectIndistinguishability_iff_card (scheme := scheme)).2 ?_
    intro adv m₁ m₂
    have hTerm :
        ∀ c : { c : Ciph // adv c = true },
          ciphertextCount scheme m₁ c.1 = ciphertextCount scheme m₂ c.1 := by
      intro c
      simpa using hCount m₁ m₂ c.1
    have hSum :
        (∑ c : { c : Ciph // adv c = true }, ciphertextCount scheme m₁ c.1) =
          ∑ c : { c : Ciph // adv c = true }, ciphertextCount scheme m₂ c.1 := by
      simpa using congrArg
        (fun f :
            { c : Ciph // adv c = true } → ℕ =>
              ∑ c : { c : Ciph // adv c = true }, f c) (funext hTerm)
    simpa [adversaryWinCount_eq_sum (scheme := scheme)] using hSum
  · intro h
    have hCount :=
      (perfectIndistinguishability_iff_card (scheme := scheme)).1 h
    refine
      (perfectSecrecy_iff_card (scheme := scheme)).2 ?_
    intro m₁ m₂ c₀
    classical
    let adv : Ciph → Bool := fun c => if c = c₀ then true else false
    have hAdv :
        adversaryWinCount scheme adv m₁ =
          adversaryWinCount scheme adv m₂ := hCount adv m₁ m₂
    have hWin :
        ∀ m, adversaryWinCount scheme adv m = ciphertextCount scheme m c₀ := by
      intro m
      unfold adversaryWinCount ciphertextCount
      simp [adv]
    have hWin₁ := hWin m₁
    have hWin₂ := hWin m₂
    simpa [hWin₁, hWin₂] using hAdv

end

section
variable [Fintype Key] [DecidableEq Ciph]
variable [Nonempty Key] [Fintype Ciph]
variable [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

theorem perfectSecrecy_iff_perfectImitatability
    (scheme : SymmetricEncryption Key Msg Ciph) :
    perfectSecrecy scheme ↔ perfectImitatability scheme := by
  classical
  constructor
  · intro h
    have hInd :=
      (perfectSecrecy_iff_perfectIndistinguishability
        (scheme := scheme)).1 h
    refine fun {α : Type _} [Fintype α] [DecidableEq α] (adv : Ciph → α) => ?_
    classical
    obtain ⟨base⟩ := (inferInstance : Nonempty Msg)
    refine
      ⟨{ prob := fun a => adversaryOutputProbability scheme adv base a
          , nonneg := by
              intro a
              exact adversaryOutputProbability_nonneg
                (scheme := scheme) (adv := adv) base a
          , sum_one :=
              adversaryOutputProbability_sum
                (scheme := scheme) (adv := adv) base },
        ?_⟩
    intro μ a
    have hConst :
        ∀ m, adversaryOutputProbability scheme adv m a =
            adversaryOutputProbability scheme adv base a := by
      intro m
      have :=
        hInd (fun c => decide (adv c = a)) m base
      simpa [adversaryOutputProbability_eq_winProbability]
        using this
    have hμ := μ.sum_one
    have hSumEq :
        (∑ m : Msg, μ.prob m *
            adversaryOutputProbability scheme adv m a) =
          (∑ m : Msg, μ.prob m) *
            adversaryOutputProbability scheme adv base a := by
      classical
      calc
        (∑ m : Msg, μ.prob m *
            adversaryOutputProbability scheme adv m a) =
            ∑ m : Msg, μ.prob m *
              adversaryOutputProbability scheme adv base a := by
                simp [hConst]
        _ = (∑ m : Msg, μ.prob m) *
            adversaryOutputProbability scheme adv base a := by
              simpa using
                (sum_mul_right (f := fun m : Msg => μ.prob m)
                  (c := adversaryOutputProbability scheme adv base a))
    have hSum :
        (∑ m : Msg, μ.prob m *
            adversaryOutputProbability scheme adv m a) =
          adversaryOutputProbability scheme adv base a := by
      simpa [hμ] using hSumEq
    simp [adversaryOutputProbabilityWithMessageDistribution, hSum]
  · intro h
    have hInd :
        perfectIndistinguishability scheme := by
      intro adv m₁ m₂
      obtain ⟨dist, hdist⟩ :=
        h (α := Bool) adv
      have h₁ :
          adversaryWinProbability scheme adv m₁ = dist.prob true := by
        have := hdist (FiniteDistribution.dirac m₁) true
        have hOut :
            adversaryOutputProbability scheme adv m₁ true = dist.prob true := by
          simpa [adversaryOutputProbabilityWithMessageDistribution_dirac]
            using this
        simpa [adversaryOutputProbability_eq_winProbability] using hOut
      have h₂ :
          adversaryWinProbability scheme adv m₂ = dist.prob true := by
        have := hdist (FiniteDistribution.dirac m₂) true
        have hOut :
            adversaryOutputProbability scheme adv m₂ true = dist.prob true := by
          simpa [adversaryOutputProbabilityWithMessageDistribution_dirac]
            using this
        simpa [adversaryOutputProbability_eq_winProbability] using hOut
      simp [h₁, h₂]
    exact
      (perfectSecrecy_iff_perfectIndistinguishability
        (scheme := scheme)).2 hInd

end

end Secrecy
