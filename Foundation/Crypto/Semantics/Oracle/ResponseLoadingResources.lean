import Foundation.Crypto.Semantics.Oracle.ResponseLoading
import Foundation.Crypto.Semantics.Oracle.EncodedStorage
import Foundation.Crypto.Semantics.Asymptotic.PolynomiallyBounded

/-! Scheme-independent storage bounds for the actual response-loading prefix.
The prefix stops when the saved machine resumes, before executing its next
instruction. Every intermediate response list, tape, saved machine, external
state and transcript is retained in the measured configuration. -/
namespace CryptoOracle.Interactive.ResponseLoading.Resources
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

/-- Analysis boundary at the end of loading, before the resumed instruction. -/
def boundary : Control → Bool
  | .loading _ _ _ | .advancing _ _ _ | .rewinding _ _ => false
  | _ => true

/-- Freeze only the completed prefix. Before the boundary this is exactly the
existing operational transition, with no extra runtime instruction. -/
noncomputable def step {State : Type u} (code : Code) (oracle : BitOracle State)
    (frame : Configuration State) : PMF (Configuration State) :=
  if boundary frame.control then PMF.pure frame else Reification.timedStep code oracle frame

def phase : Control → Prop
  | .loading _ _ _ | .advancing _ _ _ | .rewinding _ _ | .running _ => True
  | _ => False

theorem step_before_boundary {State : Type u} (code : Code) (oracle : BitOracle State)
    (frame : Configuration State) (h : boundary frame.control = false) :
    step code oracle frame = Reification.timedStep code oracle frame := by simp [step, h]

/-- Loading itself invokes no oracle and executes no source instruction. -/
theorem step_independent {State : Type u} (code otherCode : Code)
    (oracle otherOracle : BitOracle State) (frame : Configuration State) :
    step code oracle frame = step otherCode otherOracle frame := by
  rcases frame with ⟨state, control, trace⟩
  cases control with
  | loading machine remaining tape =>
      cases remaining <;> simp [step, boundary, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition]
  | rewinding machine tape =>
      cases hl : tape.left <;> simp [step, boundary, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, hl]
  | advancing machine remaining tape =>
      simp [step, boundary, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition]
  | _ => simp [step, boundary]

/-- A loading transition preserves the external state, transcript and saved
program counter. At most one represented tape cell is added per transition. -/
theorem local_bound {State : Type u} (stateSize : State → Nat)
    (code : Code) (oracle : BitOracle State) (start next : Configuration State)
    (hPhase : phase start.control) (h : next ∈ (step code oracle start).support) :
    phase next.control ∧ next.state = start.state ∧ next.reverseTrace = start.reverseTrace ∧
    ConfigurationEncoding.pc next.control = ConfigurationEncoding.pc start.control ∧
    SourceStorage.cells stateSize next ≤ SourceStorage.cells stateSize start + 1 := by
  rcases start with ⟨state, control, trace⟩
  cases control with
  | running machine =>
      simp [step, boundary] at h
      subst next
      exact ⟨trivial, rfl, rfl, rfl, by omega⟩
  | loading machine remaining tape =>
      cases remaining <;>
        simp [step, boundary, Reification.timedStep, Reification.terminal,
          Reification.perform, Reification.action, transition] at h <;> subst next <;>
        simp [phase, ConfigurationEncoding.pc, SourceStorage.cells, SourceStorage.controlCells,
          Tape.cells_write] <;> omega
  | advancing machine remaining tape =>
      simp [step, boundary, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition] at h
      subst next
      have ht := Tape.cells_moveRight_le tape
      simp [phase, ConfigurationEncoding.pc, SourceStorage.cells, SourceStorage.controlCells]
      omega
  | rewinding machine tape =>
      cases hl : tape.left with
      | nil =>
          simp [step, boundary, Reification.timedStep, Reification.terminal,
            Reification.perform, Reification.action, transition, hl] at h
          subst next
          simp [phase, ConfigurationEncoding.pc, SourceStorage.cells, SourceStorage.controlCells,
            Machine.Configuration.tapeCells]
          omega
      | cons head rest =>
          simp [step, boundary, Reification.timedStep, Reification.terminal,
            Reification.perform, Reification.action, transition, hl] at h
          subst next
          have ht := Tape.cells_moveLeft_le tape
          simp [phase, ConfigurationEncoding.pc, SourceStorage.cells, SourceStorage.controlCells]
          omega
  | sending => exact False.elim hPhase
  | reversing => exact False.elim hPhase
  | awaiting => exact False.elim hPhase
  | finished => exact False.elim hPhase

/-- All prefixes, including incomplete loads, preserve the environment. -/
theorem prefix_bound {State : Type u} (stateSize : State → Nat)
    (code : Code) (oracle : BitOracle State) (elapsed : Nat)
    (start next : Configuration State) (hPhase : phase start.control)
    (h : next ∈ (TimedExecution.eval (step code oracle) elapsed start).support) :
    phase next.control ∧ next.state = start.state ∧ next.reverseTrace = start.reverseTrace ∧
    ConfigurationEncoding.pc next.control = ConfigurationEncoding.pc start.control ∧
    SourceStorage.cells stateSize next ≤ SourceStorage.cells stateSize start + elapsed := by
  have hb := ResourceGrowth.invariant_endpoint (step code oracle) (SourceStorage.cells stateSize)
    (fun frame => phase frame.control ∧ frame.state = start.state ∧
      frame.reverseTrace = start.reverseTrace ∧
      ConfigurationEncoding.pc frame.control = ConfigurationEncoding.pc start.control) 1
    (by
      intro before hv after ha
      obtain ⟨hp, hs, ht, hc, hb⟩ := local_bound stateSize code oracle before after hv.1 ha
      exact ⟨⟨hp, hs.trans hv.2.1, ht.trans hv.2.2.1, hc.trans hv.2.2.2⟩, hb⟩)
    elapsed start next ⟨hPhase, rfl, rfl, rfl⟩ h
  exact ⟨hb.1.1, hb.1.2.1, hb.1.2.2.1, hb.1.2.2.2, by simpa using hb.2⟩

def bound (initialPc initialCells traceLength horizon : Nat) : Nat :=
  8 * initialPc + 72 * (initialCells + horizon) + 4 * traceLength + 100

/-- A faithful, decodable encoding of the whole loading configuration is
bounded at every supported prefix. No oracle growth assumption is needed. -/
theorem encoded_peak {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : Code) (oracle : BitOracle State) (horizon elapsed : Nat) (hTime : elapsed ≤ horizon)
    (start next : Configuration State) (hPhase : phase start.control)
    (h : next ∈ (TimedExecution.eval (step code oracle) elapsed start).support) :
    ((ConfigurationEncoding.frame E).encode next).length ≤
      bound (ConfigurationEncoding.pc start.control) (SourceStorage.cells stateSize start)
        start.reverseTrace.length horizon := by
  obtain ⟨_, _, ht, hc, hb⟩ := prefix_bound stateSize code oracle elapsed start next hPhase h
  have he := ConfigurationEncoding.frame_length_le E stateSize hState next
  rw [ht, hc] at he
  unfold bound
  omega


/-- The analysis prefix has exactly the original machine's first-arrival
state/cost distribution, even when the resumed machine keeps running. -/
theorem boundary_law {State : Type u} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (start : Configuration State) :
    runToBoundary (Reification.timedStep code oracle) (fun frame => boundary frame.control) fuel start =
      runToBoundary (step code oracle) (fun frame => boundary frame.control) fuel start := by
  have h := runToBoundary_map (step code oracle) (Reification.timedStep code oracle)
    (fun frame => boundary frame.control) (fun frame => boundary frame.control) id
    (fun _ => rfl)
    (fun frame hb => by simp only [PMF.map_id]; exact (step_before_boundary code oracle frame hb).symm)
    fuel start
  change runToBoundary (Reification.timedStep code oracle) _ fuel start =
    (runToBoundary (step code oracle) _ fuel start).map id at h
  simpa only [PMF.map_id] using h

/-- First-arrival resource accounting for the original operational loader.
Only transitions actually used are charged, with no absorbing-exit premise. -/
theorem boundary_prefix {State : Type u} (stateSize : State → Nat)
    (code : Code) (oracle : BitOracle State) (fuel : Nat)
    (start : Configuration State) (result : Configuration State × Nat)
    (hPhase : phase start.control)
    (h : result ∈ (runToBoundary (Reification.timedStep code oracle)
      (fun frame => boundary frame.control) fuel start).support) :
    phase result.1.control ∧ result.1.state = start.state ∧
    result.1.reverseTrace = start.reverseTrace ∧
    ConfigurationEncoding.pc result.1.control = ConfigurationEncoding.pc start.control ∧
    SourceStorage.cells stateSize result.1 ≤ SourceStorage.cells stateSize start + result.2 := by
  rw [boundary_law] at h
  have hb := ResourceGrowth.invariant_boundary_endpoint (step code oracle) (SourceStorage.cells stateSize)
    (fun frame => phase frame.control ∧ frame.state = start.state ∧
      frame.reverseTrace = start.reverseTrace ∧
      ConfigurationEncoding.pc frame.control = ConfigurationEncoding.pc start.control) 1
    (by
      intro before hv after ha
      obtain ⟨hp, hs, ht, hc, hb⟩ := local_bound stateSize code oracle before after hv.1 ha
      exact ⟨⟨hp, hs.trans hv.2.1, ht.trans hv.2.2.1, hc.trans hv.2.2.2⟩, hb⟩)
    (fun frame => boundary frame.control) fuel start result ⟨hPhase, rfl, rfl, rfl⟩ h
  exact ⟨hb.1.1, hb.1.2.1, hb.1.2.2.1, hb.1.2.2.2, by simpa using hb.2⟩

/-- Bound the faithful encoding at the actual first-arrival cost. -/
theorem encoded_boundary {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : Code) (oracle : BitOracle State) (fuel : Nat)
    (start : Configuration State) (result : Configuration State × Nat)
    (hPhase : phase start.control)
    (h : result ∈ (runToBoundary (Reification.timedStep code oracle)
      (fun frame => boundary frame.control) fuel start).support) :
    ((ConfigurationEncoding.frame E).encode result.1).length ≤
      bound (ConfigurationEncoding.pc start.control) (SourceStorage.cells stateSize start)
        start.reverseTrace.length result.2 := by
  obtain ⟨_, _, ht, hc, hb⟩ := boundary_prefix stateSize code oracle fuel start result hPhase h
  have he := ConfigurationEncoding.frame_length_le E stateSize hState result.1
  rw [ht, hc] at he
  unfold bound
  omega

/-- Independent public profiles for saved addresses, stored data, transcript
entry counts and elapsed time may all vary polynomially. -/
theorem bound_polynomial {initialPc initialCells traceLength horizon : Nat → Nat}
    (hPc : PolynomiallyBounded initialPc) (hCells : PolynomiallyBounded initialCells)
    (hTrace : PolynomiallyBounded traceLength) (hTime : PolynomiallyBounded horizon) :
    PolynomiallyBounded (fun n => bound (initialPc n) (initialCells n) (traceLength n) (horizon n)) :=
  ((((PolynomiallyBounded.const 8).mul hPc).add
    ((PolynomiallyBounded.const 72).mul (hCells.add hTime))).add
      ((PolynomiallyBounded.const 4).mul hTrace)).add (PolynomiallyBounded.const 100)

/-- The existing loader reaches the resume boundary within its proven budget.
The saved source machine need not halt or absorb at that boundary. -/
theorem completes {State : Type u} (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (response : List Bool)
    (result : Configuration State × Nat)
    (h : result ∈ (runToBoundary (Reification.timedStep code oracle)
      (fun frame => boundary frame.control) (3 * response.length + 2)
      ⟨state, .loading machine response {}, trace⟩).support) :
    boundary result.1.control = true := by
  apply runToBoundary_completes (Reification.timedStep code oracle)
    (fun frame => boundary frame.control) (3 * response.length + 2)
    ⟨state, .loading machine response {}, trace⟩ _ result h
  intro target ht
  rw [ResponseLoading.run, PMF.mem_support_pure_iff] at ht
  subst target
  rfl

/-- Include the actual source code once as well as the entire loading frame. -/
def completeEncoding {State : Type u} (E : FiniteBitEncoding State) :=
  EncodedStorage.codeEncoding.prod (ConfigurationEncoding.frame E)

def completeBound (code : Code) (initialPc initialCells traceLength horizon : Nat) :=
  2 * (EncodedStorage.codeEncoding.encode code).length +
    bound initialPc initialCells traceLength horizon + 1

theorem complete_peak {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : Code) (oracle : BitOracle State) (horizon elapsed : Nat) (hTime : elapsed ≤ horizon)
    (start next : Configuration State) (hPhase : phase start.control)
    (h : next ∈ (TimedExecution.eval (step code oracle) elapsed start).support) :
    ((completeEncoding E).encode (code, next)).length ≤
      completeBound code (ConfigurationEncoding.pc start.control)
        (SourceStorage.cells stateSize start) start.reverseTrace.length horizon := by
  have hb := encoded_peak E stateSize hState code oracle horizon elapsed hTime start next hPhase h
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length, completeBound]
  omega

theorem complete_boundary {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : Code) (oracle : BitOracle State) (fuel : Nat)
    (start : Configuration State) (result : Configuration State × Nat)
    (hPhase : phase start.control)
    (h : result ∈ (runToBoundary (Reification.timedStep code oracle)
      (fun frame => boundary frame.control) fuel start).support) :
    ((completeEncoding E).encode (code, result.1)).length ≤
      completeBound code (ConfigurationEncoding.pc start.control)
        (SourceStorage.cells stateSize start) start.reverseTrace.length result.2 := by
  have hb := encoded_boundary E stateSize hState code oracle fuel start result hPhase h
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length, completeBound]
  omega

theorem completeBound_polynomial (code : Code)
    {initialPc initialCells traceLength horizon : Nat → Nat}
    (hPc : PolynomiallyBounded initialPc) (hCells : PolynomiallyBounded initialCells)
    (hTrace : PolynomiallyBounded traceLength) (hTime : PolynomiallyBounded horizon) :
    PolynomiallyBounded (fun n => completeBound code
      (initialPc n) (initialCells n) (traceLength n) (horizon n)) :=
  ((PolynomiallyBounded.const (2 * (EncodedStorage.codeEncoding.encode code).length)).add
    (bound_polynomial hPc hCells hTrace hTime)).add (PolynomiallyBounded.const 1)

end CryptoOracle.Interactive.ResponseLoading.Resources
