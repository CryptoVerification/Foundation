import Foundation.Crypto.Semantics.Probability.Facts

/-! Exact recovery of a stochastic state transformation. A reverse kernel
must recover each admitted input, not merely restore its marginal law.
Disjoint forward supports characterize existence of such recovery. -/
namespace Foundation.Probability.KernelRecovery
noncomputable section
variable {A B : Type}

def RecoversOn (forward : A → PMF B) (reverse : B → PMF A) (admitted : A → Prop) : Prop :=
  ∀ x, admitted x → (forward x).bind reverse = PMF.pure x

def Separated (forward : A → PMF B) (admitted : A → Prop) : Prop :=
  ∀ x, admitted x → ∀ y, admitted y → x ≠ y → Disjoint (forward x).support (forward y).support

theorem recovery_implies_separated (forward : A → PMF B) (reverse : B → PMF A)
    (admitted : A → Prop) (recovers : RecoversOn forward reverse admitted) : Separated forward admitted := by
  intro x hx y hy different
  apply Set.disjoint_left.mpr
  intro intermediate hxi hyi
  obtain ⟨result, hr⟩ := (reverse intermediate).support_nonempty
  have hxr : result ∈ ((forward x).bind reverse).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr ⟨intermediate, hxi, hr⟩
  have hyr : result ∈ ((forward y).bind reverse).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr ⟨intermediate, hyi, hr⟩
  rw [recovers x hx, PMF.mem_support_pure_iff] at hxr
  rw [recovers y hy, PMF.mem_support_pure_iff] at hyr
  exact different (hxr.symm.trans hyr)

theorem common_output_no_recovery (forward : A → PMF B) (admitted : A → Prop)
    (x y : A) (hx : admitted x) (hy : admitted y) (different : x ≠ y)
    (intermediate : B) (hxi : intermediate ∈ (forward x).support) (hyi : intermediate ∈ (forward y).support) :
    ¬ ∃ reverse, RecoversOn forward reverse admitted := by
  rintro ⟨reverse, recovers⟩
  exact Set.disjoint_left.mp (recovery_implies_separated forward reverse admitted recovers x hx y hy different) hxi hyi

variable [Nonempty A]

def decoder (forward : A → PMF B) (admitted : A → Prop) (intermediate : B) : A :=
  by
    classical
    exact if h : ∃ x, admitted x ∧ intermediate ∈ (forward x).support then Classical.choose h
      else Classical.choice inferInstance

theorem decoder_correct (forward : A → PMF B) (admitted : A → Prop)
    (separated : Separated forward admitted) (x : A) (hx : admitted x) (intermediate : B)
    (supported : intermediate ∈ (forward x).support) : decoder forward admitted intermediate = x := by
  classical
  have existsInput : ∃ y, admitted y ∧ intermediate ∈ (forward y).support := ⟨x,hx,supported⟩
  unfold decoder
  rw [dif_pos existsInput]
  have chosen := Classical.choose_spec existsInput
  by_contra different
  exact Set.disjoint_left.mp (separated _ chosen.1 x hx different) chosen.2 supported

theorem separated_has_decoder (forward : A → PMF B) (admitted : A → Prop)
    (separated : Separated forward admitted) :
    RecoversOn forward (fun intermediate => PMF.pure (decoder forward admitted intermediate)) admitted := by
  intro x hx
  calc
    _ = (forward x).bind (fun _ => PMF.pure x) := by
      apply bind_congr_of_support
      intro intermediate supported
      rw [decoder_correct forward admitted separated x hx intermediate supported]
    _ = _ := PMF.bind_const _ _

theorem exists_reverse_iff_separated (forward : A → PMF B) (admitted : A → Prop) :
    (∃ reverse, RecoversOn forward reverse admitted) ↔ Separated forward admitted :=
  ⟨fun ⟨reverse, recovers⟩ => recovery_implies_separated forward reverse admitted recovers,
    fun separated => ⟨_, separated_has_decoder forward admitted separated⟩⟩

end
end Foundation.Probability.KernelRecovery
