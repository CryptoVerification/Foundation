import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyTimedExecution

/-! Exact initialization inside the whole privacy machine. The generator
never reaches a ready store early, so the source cannot run during its budget. -/
namespace Foundation.Symmetric.EncryptThenMAC
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

namespace PrivateKeyGeneration

/-- A ready store cannot disappear under this generator's own transitions. -/
theorem no_ready_earlier (start : Control) (last fuel : Nat) (hFuel : fuel ≤ last)
    (hLast : ∀ final ∈ (eval last start).support, readyStore final = none)
    (final : Control) (hFinal : final ∈ (eval fuel start).support) :
    readyStore final = none := by
  cases final with
  | generating machine => rfl
  | rewinding tape => rfl
  | ready tape =>
      have hMem : Control.ready tape ∈ (eval last start).support := by
        rw [show last = fuel + (last - fuel) by omega, eval_add,
          PMF.mem_support_bind_iff]
        exact ⟨.ready tape, hFinal, by rw [eval_ready]; simp⟩
      have h := hLast (.ready tape) hMem
      simp [readyStore] at h

theorem initial_no_ready (markers : List Bool) (fuel : Nat)
    (hFuel : fuel < 6 * markers.length + 4) (final : Control)
    (hFinal : final ∈ (eval fuel (initial markers)).support) : readyStore final = none := by
  apply no_ready_earlier (initial markers) (6 * markers.length + 3) fuel (by omega) _ final hFinal
  intro result hResult
  rw [before_ready_run, PMF.mem_support_map_iff] at hResult
  obtain ⟨key, _, he⟩ := hResult
  subst result
  rfl

end PrivateKeyGeneration

namespace PrivacyMachine
universe u

/-- Lift a generator prefix into the real initialization control. The
hypothesis forbids a ready-state transfer strictly before this horizon. -/
theorem initializing_eval {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (generator : PrivateKeyGeneration.Control)
    (source : Source.Control) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) (fuel : Nat)
    (hNotReady : ∀ tick < fuel, ∀ final ∈ (PrivateKeyGeneration.eval tick generator).support,
      PrivateKeyGeneration.readyStore final = none) :
    eval code oracle fuel ⟨state, .initializing source generator, sourceTrace, externalTrace⟩ =
      (PrivateKeyGeneration.eval fuel generator).map (fun next =>
        ⟨state, .initializing source next, sourceTrace, externalTrace⟩) := by
  induction fuel with
  | zero => simp [eval, PrivateKeyGeneration.eval, PMF.pure_map]
  | succ fuel ih =>
      rw [eval_add,
        ih (fun tick ht => hNotReady tick (by omega)),
        PrivateKeyGeneration.eval_add, PMF.bind_map, PMF.map_bind]
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext next hNext
      have hn := hNotReady fuel (by omega) next hNext
      simp only [Function.comp_def, eval, PrivateKeyGeneration.eval,
        step, hn, PMF.bind_pure]

/-- No source instruction runs before the explicit ready-store transfer. -/
theorem initialization_before_source {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n fuel : Nat)
    (source : Source.Control) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool))
    (hFuel : fuel ≤ 12 * width n + 4) (final : Frame State)
    (hFinal : final ∈ (eval code oracle fuel
      ⟨state, .initializing source (PrivateKeyGeneration.initial
        (List.replicate (2 * width n) true)), sourceTrace, externalTrace⟩).support) :
    Timing.sourceBoundary final = false := by
  rw [initializing_eval code oracle _ source state sourceTrace externalTrace fuel
    (by
      intro tick hTick result hResult
      apply PrivateKeyGeneration.initial_no_ready _ tick _ result hResult
      simp only [List.length_replicate]
      omega), PMF.mem_support_map_iff] at hFinal
  obtain ⟨generator, _, he⟩ := hFinal
  subst final
  rfl

/-- Exact uniform key distribution and physical store at source resumption,
including the extra machine transition that transfers the ready store. -/
theorem initialization_run {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n : Nat)
    (source : Source.Control) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    eval code oracle (12 * width n + 5)
      ⟨state, .initializing source (PrivateKeyGeneration.initial
        (List.replicate (2 * width n) true)), sourceTrace, externalTrace⟩ =
      ((TableMAC.scheme width).keygen n).map (fun key =>
        ⟨state, .source (PrivateKeyGeneration.store key) source, sourceTrace, externalTrace⟩) := by
  rw [show 12 * width n + 5 = (12 * width n + 4) + 1 by omega, eval_add,
    initializing_eval code oracle _ source state sourceTrace externalTrace (12 * width n + 4)
      (by
        intro tick hTick final hFinal
        apply PrivateKeyGeneration.initial_no_ready _ tick _ final hFinal
        simp only [List.length_replicate]
        omega),
    PrivateKeyGeneration.table_key_run, PMF.map_comp, PMF.bind_map]
  simp only [Function.comp_def]
  conv_rhs => rw [PMF.map]
  congr 1
  funext key
  simp [eval, step, PrivateKeyGeneration.readyStore]

/-- Continue the actual source immediately after the single key sample.
This law holds for every remaining horizon, including repeated queries. -/
theorem initialization_then_run {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n rest : Nat)
    (source : Source.Control) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    eval code oracle (12 * width n + 5 + rest)
      ⟨state, .initializing source (PrivateKeyGeneration.initial
        (List.replicate (2 * width n) true)), sourceTrace, externalTrace⟩ =
      ((TableMAC.scheme width).keygen n).bind (fun key => eval code oracle rest
        ⟨state, .source (PrivateKeyGeneration.store key) source, sourceTrace, externalTrace⟩) := by
  rw [eval_add, initialization_run, PMF.bind_map]
  rfl

/-- Lift any subsequent source-frame stopping bound through real private
initialization. Reachable keys alone need satisfy the subsequent bound. -/
theorem initialization_haltsWithin {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n rest : Nat)
    (source : Source.Control) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool))
    (h : ∀ key ∈ ((TableMAC.scheme width).keygen n).support,
      HaltsWithin code oracle
        ⟨state, .source (PrivateKeyGeneration.store key) source, sourceTrace, externalTrace⟩ rest) :
    HaltsWithin code oracle
      ⟨state, .initializing source (PrivateKeyGeneration.initial
        (List.replicate (2 * width n) true)), sourceTrace, externalTrace⟩
      (12 * width n + 5 + rest) := by
  intro final hFinal
  rw [initialization_then_run, PMF.mem_support_bind_iff] at hFinal
  obtain ⟨key, hKey, hFinal⟩ := hFinal
  exact h key hKey final hFinal

/-- A concrete initial block whose law is proved from real machine
execution, not supplied as a realization assumption. -/
noncomputable def initializationBlock {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n : Nat)
    (source : Source.Control) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    TimedExecution.Block (step code oracle)
      ⟨state, .initializing source (PrivateKeyGeneration.initial
        (List.replicate (2 * width n) true)), sourceTrace, externalTrace⟩ where
  budget := 12 * width n + 5
  outcome := ((TableMAC.scheme width).keygen n).map (fun key =>
    (⟨state, .source (PrivateKeyGeneration.store key) source, sourceTrace, externalTrace⟩,
      12 * width n + 5))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨key, _, he⟩ := hResult
    subst result
    exact Nat.le_refl _
  law := by
    intro horizon hHorizon
    have hx := initialization_then_run code oracle width n (horizon - (12 * width n + 5))
      source state sourceTrace externalTrace
    have hh : 12 * width n + 5 + (horizon - (12 * width n + 5)) = horizon := by omega
    rw [hh] at hx
    rw [Timing.eval_eq, hx, PMF.bind_map]
    congr 1
    funext key
    exact (Timing.eval_eq code oracle _ _).symm

/-- Initialization completes at an intermediate source boundary. -/
theorem initialization_completes {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n : Nat)
    (source : Source.Control) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    (Timing.sourceBlock code oracle (12 * width n + 5)
      ⟨state, .initializing source (PrivateKeyGeneration.initial
        (List.replicate (2 * width n) true)), sourceTrace, externalTrace⟩).Completes
      Timing.sourceBoundary := by
  intro result hResult
  apply TimedExecution.runToBoundary_completes (step code oracle) Timing.sourceBoundary _ _ _ result hResult
  intro final hFinal
  rw [Timing.eval_eq, initialization_run, PMF.mem_support_map_iff] at hFinal
  obtain ⟨key, _, he⟩ := hFinal
  subst final
  rfl

end PrivacyMachine
end Foundation.Symmetric.EncryptThenMAC
