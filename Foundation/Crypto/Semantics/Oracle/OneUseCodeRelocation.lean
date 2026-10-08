import Foundation.Crypto.Semantics.Oracle.CodeRelocation
import Foundation.Crypto.Semantics.Oracle.OneUseSource

/-! Relocate caller code across the complete private one-use machine.
Private preparation and native computation retain their original addresses;
only the suspended caller and public source frames are relocated. -/
namespace CryptoOracle.Interactive.CodeRelocation
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

def callback {State : Type u} (base : Nat) : NativeCallback.Control State → NativeCallback.Control State
  | .responding component => .responding component
  | .source source => .source (frame base source)

theorem callback_step {State : Type u} (before code : Code) (native : Machine.Program)
    (oracle : BitOracle State) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (source : NativeCallback.Control State) :
    NativeCallback.step native (host before code) oracle (saved.rebasePc before.length) state trace request
      (callback before.length source) =
      (NativeCallback.step native code oracle saved state trace request source).map (callback before.length) := by
  cases source with
  | responding component =>
      cases component <;> simp only [callback, NativeCallback.step, PMF.pure_map, PMF.map_comp, Function.comp_def]
      all_goals rfl
  | source source =>
      simp only [callback, NativeCallback.step, timed_step, PMF.map_comp, Function.comp_def]

def checked {State : Type u} (base : Nat) : CheckedCallback.Control State → CheckedCallback.Control State
  | .preparing preparation => .preparing preparation
  | .computing first second component => .computing first second component
  | .tagging first second packet => .tagging first second packet
  | .calling first second source => .calling first second (callback base source)

theorem checked_step {State : Type u} (before code : Code) (native : Machine.Program)
    (oracle : BitOracle State) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (source : CheckedCallback.Control State) :
    CheckedCallback.step native (host before code) oracle (saved.rebasePc before.length) state trace request
      (checked before.length source) =
      (CheckedCallback.step native code oracle saved state trace request source).map (checked before.length) := by
  cases source with
  | preparing preparation =>
      cases preparation with
      | preparing preparation =>
          cases preparation <;> simp only [checked, CheckedCallback.step, PMF.pure_map, PMF.map_comp, Function.comp_def]
          all_goals rfl
      | failure recovery =>
          cases recovery <;> simp only [checked, CheckedCallback.step, PMF.pure_map, PMF.map_comp, Function.comp_def]
          all_goals rfl
  | computing first second component =>
      cases component <;> simp only [checked, CheckedCallback.step, PMF.pure_map, PMF.map_comp, Function.comp_def]
      all_goals rfl
  | tagging first second packet =>
      cases packet <;> simp only [checked, CheckedCallback.step, PMF.pure_map, PMF.map_comp, Function.comp_def]
      all_goals rfl
  | calling first second source =>
      simp only [checked, CheckedCallback.step, callback_step, PMF.map_comp, Function.comp_def]

def oneUse {State : Type u} (base : Nat) : OneUseSource.Control State → OneUseSource.Control State
  | .source used key source => .source used key (frame base source)
  | .handling used saved state trace request handler =>
      .handling used (saved.rebasePc base) state trace request (checked base handler)

theorem one_use_step {State : Type u} (before code : Code) (native : Machine.Program)
    (oracle : BitOracle State) (source : OneUseSource.Control State) :
    OneUseSource.step native (host before code) oracle (oneUse before.length source) =
      (OneUseSource.step native code oracle source).map (oneUse before.length) := by
  cases source with
  | source used key source =>
      have hs := timed_step before code oracle source
      rcases source with ⟨state, sourceControl, trace⟩
      cases sourceControl <;>
        simp only [oneUse, frame, control, OneUseSource.step, PMF.pure_map]
      all_goals first
        | (cases used <;> rfl)
        | (simp only [frame, control] at hs; rw [hs]; simp only [PMF.map_comp, Function.comp_def]; rfl)
  | handling used saved state trace request handler =>
      have hc := checked_step before code native oracle saved state trace request handler
      cases handler with
      | preparing preparation =>
          cases preparation with
          | preparing preparation =>
              cases preparation <;> cases used <;>
                simp only [oneUse, checked, OneUseSource.step, Bool.false_eq_true, ↓reduceIte, PMF.pure_map]
              all_goals first
                | rfl
                | (simp only [checked] at hc; rw [hc]; simp only [PMF.map_comp, Function.comp_def]; rfl)
          | failure recovery =>
              cases recovery <;> simp only [oneUse, checked, OneUseSource.step]
              all_goals simp only [checked] at hc; rw [hc]; simp only [PMF.map_comp, Function.comp_def]; rfl
      | computing first second component =>
          simp only [oneUse, checked, OneUseSource.step]
          simp only [checked] at hc
          rw [hc]
          simp only [PMF.map_comp, Function.comp_def]
          rfl
      | tagging first second packet =>
          simp only [oneUse, checked, OneUseSource.step]
          simp only [checked] at hc
          rw [hc]
          simp only [PMF.map_comp, Function.comp_def]
          rfl
      | calling first second source =>
          cases source with
          | responding component =>
              simp only [oneUse, checked, callback, OneUseSource.step]
              simp only [checked, callback] at hc
              rw [hc]
              simp only [PMF.map_comp, Function.comp_def]
              rfl
          | source source =>
              rcases source with ⟨currentState, sourceControl, currentTrace⟩
              cases sourceControl <;>
                simp only [oneUse, checked, callback, frame, control, OneUseSource.step, PMF.pure_map]
              all_goals first
                | rfl
                | (simp only [checked, callback, frame, control] at hc; rw [hc]; simp only [PMF.map_comp, Function.comp_def]; rfl)

theorem one_use_eval {State : Type u} (before code : Code) (native : Machine.Program)
    (oracle : BitOracle State) (fuel : Nat) (source : OneUseSource.Control State) :
    TimedExecution.eval (OneUseSource.step native (host before code) oracle) fuel (oneUse before.length source) =
      (TimedExecution.eval (OneUseSource.step native code oracle) fuel source).map (oneUse before.length) := by
  symm
  exact eval_map _ _ (oneUse before.length) (fun source => (one_use_step before code native oracle source).symm) fuel source

theorem used {State : Type u} (base : Nat) (source : OneUseSource.Control State) :
    OneUseSource.used (oneUse base source) = OneUseSource.used source := by
  cases source <;> rfl

theorem accepted {State : Type u} (base : Nat) (source : OneUseSource.Control State) :
    OneUseSource.accepted (oneUse base source) = OneUseSource.accepted source := by
  cases source with
  | source used key frame => rfl
  | handling used saved state trace request handler =>
      cases used <;> cases handler <;> simp only [oneUse, checked, OneUseSource.accepted]
      rename_i preparation
      cases preparation with
      | preparing preparation => cases preparation <;> rfl
      | failure recovery => rfl

noncomputable def oneUseProcedure {State : Type u} {Input Output : Type*} (before code : Code)
    (native : Machine.Program) (oracle : BitOracle State)
    (P : Procedure (OneUseSource.step native code oracle) Input Output) :=
  P.transport (OneUseSource.step native (host before code) oracle) (oneUse before.length)
    (one_use_step before code native oracle)

theorem oneUseProcedure_budget {State : Type u} {Input Output : Type*} (before code : Code)
    (native : Machine.Program) (oracle : BitOracle State)
    (P : Procedure (OneUseSource.step native code oracle) Input Output) (input : Input) :
    (oneUseProcedure before code native oracle P).budget input = P.budget input := rfl

theorem oneUseProcedure_costed {State : Type u} {Input Output : Type*} (before code : Code)
    (native : Machine.Program) (oracle : BitOracle State)
    (P : Procedure (OneUseSource.step native code oracle) Input Output) (input : Input) :
    (oneUseProcedure before code native oracle P).costed input = P.costed input := rfl

end CryptoOracle.Interactive.CodeRelocation
