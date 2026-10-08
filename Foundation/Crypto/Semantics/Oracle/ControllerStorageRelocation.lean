import Foundation.Crypto.Semantics.Oracle.ControllerStorage
import Foundation.Crypto.Semantics.Oracle.OneUseCodeRelocation

/-! The complete retained-data measure is invariant under caller relocation.
Code length and integer address representations remain separate resources. -/
namespace CryptoOracle.Interactive.CodeRelocation
open Foundation.Probability
universe u
variable {State : Type u}

theorem callback_cells (stateSize : State → Nat) (base : Nat) (source : NativeCallback.Control State) :
    ControllerStorage.callbackCells stateSize (callback base source) =
      ControllerStorage.callbackCells stateSize source := by
  cases source <;> simp only [callback, ControllerStorage.callbackCells, cells]

theorem checked_cells (stateSize : State → Nat) (base : Nat) (source : CheckedCallback.Control State) :
    ControllerStorage.checkedCells stateSize (checked base source) =
      ControllerStorage.checkedCells stateSize source := by
  cases source <;> simp only [checked, ControllerStorage.checkedCells, callback_cells]

theorem one_use_cells (stateSize : State → Nat) (base : Nat) (source : OneUseSource.Control State) :
    ControllerStorage.sourceCells stateSize (oneUse base source) =
      ControllerStorage.sourceCells stateSize source := by
  cases source <;> simp only [oneUse, ControllerStorage.sourceCells, cells, checked_cells,
    Machine.Configuration.tapeCells, Machine.Configuration.rebasePc]

/-- A bound for every supported state at an inspected prefix transfers to the
relocated physical machine, including its complete private controller data. -/
theorem one_use_storage_bound (stateSize : State → Nat) (before code : Code)
    (native : Machine.Program) (oracle : BitOracle State) (elapsed : Nat)
    (start intermediate : OneUseSource.Control State) (cap : Nat)
    (hBound : ∀ result ∈ (TimedExecution.eval (OneUseSource.step native code oracle) elapsed start).support,
      ControllerStorage.sourceCells stateSize result ≤ cap)
    (h : intermediate ∈ (TimedExecution.eval (OneUseSource.step native (host before code) oracle)
      elapsed (oneUse before.length start)).support) :
    ControllerStorage.sourceCells stateSize intermediate ≤ cap := by
  rw [one_use_eval, PMF.mem_support_map_iff] at h
  obtain ⟨source, hs, he⟩ := h
  subst intermediate
  rw [one_use_cells]
  exact hBound source hs

end CryptoOracle.Interactive.CodeRelocation
