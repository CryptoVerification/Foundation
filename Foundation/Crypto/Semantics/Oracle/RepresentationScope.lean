import Foundation.Crypto.Semantics.Oracle.RepresentationSwitch

/-! Scope facts needed BEFORE applying a representation edit to a real
execution prefix. Both the saved cache keys and the captured continuation
stay inside the original query footprint plus initial cache keys. -/
namespace CryptoOracle.RandomOracle.Representation.Scope
open Foundation.Probability
variable {Input Response Stored Result : Type} [DecidableEq Input] [Fintype Response] [Nonempty Response]

def keysWithin (allowed : Finset Input) (saved : Table Input Stored) : Prop :=
  ∀ entry ∈ saved, entry.1 ∈ allowed

theorem step_keys (codec : Input → Response ≃ Stored) (allowed : Finset Input)
    (saved : Table Input Stored) (initial : keysWithin allowed saved) (input : Input) (included : input ∈ allowed)
    (answer : Table Input Stored × Response) (supported : answer ∈ (oracle codec saved input).support) :
    keysWithin allowed answer.1 := by
  cases found : saved.lookup input with
  | some stored =>
      simp only [oracle, found, PMF.mem_support_pure_iff] at supported
      subst answer
      exact initial
  | none =>
      simp only [oracle, found, PMF.mem_support_map_iff] at supported
      obtain ⟨value, _, rfl⟩ := supported
      intro entry member
      rcases List.mem_cons.mp member with same | old
      · subst entry; exact included
      · exact initial entry old

theorem run_keys (codec : Input → Response ≃ Stored) (allowed : Finset Input)
    (program : Program Input Response Result) (within : program.footprint ⊆ allowed)
    (saved : Table Input Stored) (initial : keysWithin allowed saved)
    (out : Outcome Input Response Result (Table Input Stored))
    (supported : out ∈ (program.run (oracle codec) saved).support) : keysWithin allowed out.state := by
  induction program generalizing saved out with
  | done result =>
      simp only [Program.run, PMF.mem_support_pure_iff] at supported
      subst out
      exact initial
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at supported
      obtain ⟨bit, _, tail⟩ := supported
      apply ih bit _ saved initial out tail
      intro input member
      apply within
      cases bit with
      | false => exact Finset.mem_union_left _ member
      | true => exact Finset.mem_union_right _ member
  | query input next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at supported
      obtain ⟨answer, answered, tail⟩ := supported
      rw [PMF.mem_support_map_iff] at tail
      obtain ⟨last, reachable, rfl⟩ := tail
      exact ih answer.2 (fun _ member => within (Program.continuation_subset input next answer.2 member))
        answer.1 (step_keys codec allowed saved initial input (within (Finset.mem_insert_self _ _)) answer answered)
        last reachable

omit [Nonempty Response] in
theorem pause_footprint (count : Nat) (program : Program Input Response Result) :
    (Program.pauseAfter count program).footprint ⊆ program.footprint := by
  intro input member
  obtain ⟨position, small, member⟩ := ((Program.pauseAfter_bounded count program).footprint_positions input).mp member
  rw [Program.pauseAfter_footprintAt, if_pos small] at member
  exact Program.footprintAt_subset position program member

omit [Nonempty Response] in
theorem remaining_footprint {State : Type} (world : Oracle Input Response State)
    (program : Program Input Response Result) (count : Nat) (state : State)
    (past : Outcome Input Response (Program Input Response Result) State)
    (supported : past ∈ ((Program.pauseAfter count program).run world state).support) :
    past.result.footprint ⊆ program.footprint := by
  induction program generalizing count state past with
  | done result =>
      cases count <;> simp only [Program.pauseAfter, Program.run, PMF.mem_support_pure_iff] at supported
      all_goals subst past; exact Finset.Subset.refl _
  | coin next ih =>
      cases count with
      | zero =>
          simp only [Program.pauseAfter, Program.run, PMF.mem_support_pure_iff] at supported
          subst past
          exact Finset.Subset.refl _
      | succ count =>
          rw [Program.pauseAfter, Program.run, PMF.mem_support_bind_iff] at supported
          obtain ⟨bit, _, tail⟩ := supported
          intro input member
          have inner := ih bit (count + 1) state past tail member
          cases bit with
          | false => exact Finset.mem_union_left _ inner
          | true => exact Finset.mem_union_right _ inner
  | query input next ih =>
      cases count with
      | zero =>
          simp only [Program.pauseAfter, Program.run, PMF.mem_support_pure_iff] at supported
          subst past
          exact Finset.Subset.refl _
      | succ count =>
          rw [Program.pauseAfter, Program.run, PMF.mem_support_bind_iff] at supported
          obtain ⟨answer, _, tail⟩ := supported
          rw [PMF.mem_support_map_iff] at tail
          obtain ⟨last, reachable, rfl⟩ := tail
          exact (ih answer.2 count answer.1 last reachable).trans (Program.continuation_subset input next answer.2)

def allowed (program : Program Input Response Result) (saved : Table Input Stored) : Finset Input :=
  program.footprint ∪ (saved.map Prod.fst).toFinset

omit [Nonempty Response] in
theorem initial_keys (program : Program Input Response Result) (saved : Table Input Stored) :
    keysWithin (allowed program saved) saved := by
  intro entry member
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem member))

theorem prefix_scope (codec : Input → Response ≃ Stored) (program : Program Input Response Result)
    (count : Nat) (saved : Table Input Stored) (past : Switch.Past Input Response Result Stored)
    (supported : past ∈ ((Program.pauseAfter count program).run (oracle codec) saved).support) :
    keysWithin (allowed program saved) past.state ∧ past.result.footprint ⊆ allowed program saved := by
  have upper : program.footprint ⊆ allowed program saved := Finset.subset_union_left
  exact ⟨run_keys codec _ _ ((pause_footprint count program).trans upper) saved (initial_keys program saved) past supported,
    (remaining_footprint (oracle codec) program count saved past supported).trans upper⟩

end CryptoOracle.RandomOracle.Representation.Scope
