import Foundation.Crypto.Semantics.Oracle.NativeCode
import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! Cell equivalence for the interactive machine. Native and request-scanning
 tapes may have redundant outer blanks. Response-loading tapes are related
 by literal equality: their rewind controller inspects the represented left
 list, so cell equivalence alone would not preserve its transition count.
 No normalization of either execution is performed. -/
namespace CryptoOracle.Interactive.CellEquivalence
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

inductive Related : Control → Control → Prop where
  | running {c d} : c.Equivalent d → Related (.running c) (.running d)
  | sending {c d t s bits} : c.Equivalent d → t.Equivalent s →
      Related (.sending c t bits) (.sending d s bits)
  | reversing {c d remaining bits} : c.Equivalent d →
      Related (.reversing c remaining bits) (.reversing d remaining bits)
  | awaiting {c d request} : c.Equivalent d → Related (.awaiting c request) (.awaiting d request)
  | loading {c d remaining tape} : c.Equivalent d →
      Related (.loading c remaining tape) (.loading d remaining tape)
  | advancing {c d remaining tape} : c.Equivalent d →
      Related (.advancing c remaining tape) (.advancing d remaining tape)
  | rewinding {c d tape} : c.Equivalent d → Related (.rewinding c tape) (.rewinding d tape)
  | finished (bit) : Related (.finished bit) (.finished bit)

def Frames {State : Type*} (c d : Configuration State) : Prop :=
  c.state = d.state ∧ c.reverseTrace = d.reverseTrace ∧ Related c.control d.control

theorem terminal {c d : Control} (h : Related c d) :
    Reification.terminal c = Reification.terminal d := by
  cases h with
  | running he => exact he.2.1
  | _ => rfl

private def eraseCalls (code : Code) : Machine.Program :=
  code.map fun | .native i => i | .call => .halt

private theorem native_perform {State : Type*} (code : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (c : Machine.Configuration)
    (instruction : Machine.Instruction) (active : c.halted = false)
    (lookup : code[c.pc]? = some (.native instruction)) :
    Reification.perform code oracle (NativeCode.frame state trace c) =
      (Machine.stepPMF (eraseCalls code) c).map (NativeCode.frame state trace) := by
  have decoded : (eraseCalls code)[c.pc]? = some instruction := by
    simp [eraseCalls, List.getElem?_map, lookup]
  cases hn : instruction.next c with
  | inl next =>
      simp [Reification.perform, Reification.action, transition, NativeCode.frame,
        active, lookup, Machine.stepPMF, Machine.next, decoded, hn, PMF.pure_map]
  | inr pair =>
      simp [Reification.perform, Reification.action, transition, NativeCode.frame,
        active, lookup, Machine.stepPMF, Machine.next, decoded, hn,
        PMF.map_comp, Function.comp_def]
      congr 1
      funext bit
      cases bit <;> rfl

/-- Equal invariant continuations have equal probabilities after a real
interactive transition, including a shared oracle response and local coins. -/
theorem perform_bind {State α : Type*} (code : Code) (oracle : BitOracle State)
    (c d : Configuration State) (h : Frames c d) (k : Configuration State → PMF α)
    (hk : ∀ c d, Frames c d → k c = k d) :
    (Reification.perform code oracle c).bind k =
      (Reification.perform code oracle d).bind k := by
  rcases c with ⟨state, control, trace⟩
  rcases d with ⟨other, otherControl, otherTrace⟩
  rcases h with ⟨rfl, rfl, h⟩
  have finish {a b : Control} (h : Related a b) :
      k ⟨state, a, trace⟩ = k ⟨state, b, trace⟩ := hk _ _ ⟨rfl, rfl, h⟩
  cases h with
  | running h =>
      rename_i c d
      cases active : c.halted with
      | true =>
          have hd : d.halted = true := h.2.1.symm.trans active
          simp [Reification.perform, Reification.action, transition, active, hd,
            ← h.2.2.2.1]
      | false =>
          have hd : d.halted = false := h.2.1.symm.trans active
          cases lookup : code[c.pc]? with
          | none =>
              have otherLookup : code[d.pc]? = none := by simpa [← h.1] using lookup
              simp [Reification.perform, Reification.action, transition, active, hd, lookup, otherLookup]
          | some instruction =>
              have otherLookup : code[d.pc]? = some instruction := by simpa [← h.1] using lookup
              cases instruction with
              | call =>
                  simpa [Reification.perform, Reification.action, transition, active, hd, lookup, otherLookup] using
                    finish (.sending h.advance h.2.2.2)
              | native instruction =>
                  change (Reification.perform code oracle (NativeCode.frame state trace c)).bind k =
                    (Reification.perform code oracle (NativeCode.frame state trace d)).bind k
                  rw [native_perform code oracle state trace c instruction active lookup,
                    native_perform code oracle state trace d instruction hd otherLookup,
                    PMF.bind_map, PMF.bind_map]
                  exact Machine.stepPMF_bind_eq_of_equivalent _ c d h _
                    (fun _ _ he => finish (.running he))
  | sending h ht =>
      rename_i c d t s bits
      cases current : t.current with
      | none =>
          simpa [Reification.perform, Reification.action, transition, current, ← ht.1] using
            finish (.reversing h)
      | some bit =>
          simpa [Reification.perform, Reification.action, transition, current, ← ht.1] using
            finish (.sending h ht.moveRight)
  | reversing h =>
      rename_i c d remaining bits
      cases remaining <;>
        simpa [Reification.perform, Reification.action, transition] using
          finish (by first | exact Related.awaiting h | exact Related.reversing h)
  | awaiting h =>
      simp only [Reification.perform, Reification.action, transition, PMF.bind_map]
      congr 1
      funext response
      exact hk _ _ ⟨rfl, rfl, .loading h⟩
  | loading h =>
      rename_i c d remaining tape
      cases remaining <;>
        simpa [Reification.perform, Reification.action, transition] using
          finish (by first | exact Related.rewinding h | exact Related.advancing h)
  | advancing h =>
      simpa [Reification.perform, Reification.action, transition] using finish (.loading h)
  | rewinding h =>
      rename_i c d tape
      cases left : tape.left with
      | nil =>
          have he : ({ c with outputTape := tape } : Machine.Configuration).Equivalent
              { d with outputTape := tape } := ⟨h.1, h.2.1, h.2.2.1, Tape.Equivalent.refl _⟩
          simpa [Reification.perform, Reification.action, transition, left] using finish (.running he)
      | cons cell rest =>
          simpa [Reification.perform, Reification.action, transition, left] using finish (.rewinding (tape := tape.moveLeft) h)
  | finished bit => simp [Reification.perform, Reification.action, transition]

/-- Stopping on a native halt preserves the same relation. -/
theorem timed_bind {State α : Type*} (code : Code) (oracle : BitOracle State)
    (c d : Configuration State) (h : Frames c d) (k : Configuration State → PMF α)
    (hk : ∀ c d, Frames c d → k c = k d) :
    (Reification.timedStep code oracle c).bind k =
      (Reification.timedStep code oracle d).bind k := by
  have ht := terminal h.2.2
  cases hb : Reification.terminal c.control with
  | true => simpa [Reification.timedStep, ← ht, hb] using hk c d h
  | false => simpa [Reification.timedStep, ← ht, hb] using perform_bind code oracle c d h k hk

/-- Any cell-invariant observation of the whole execution has exactly the
same law, retaining the oracle state and complete query history. -/
theorem eval_map {State α : Type*} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (c d : Configuration State) (h : Frames c d)
    (observe : Configuration State → α)
    (ho : ∀ c d, Frames c d → observe c = observe d) :
    (Reification.eval code oracle fuel c).map observe =
      (Reification.eval code oracle fuel d).map observe := by
  rw [← Reification.timed_eval_eq, ← Reification.timed_eval_eq]
  induction fuel generalizing c d with
  | zero => simp [TimedExecution.eval, PMF.pure_map, ho c d h]
  | succ fuel ih =>
      rw [TimedExecution.eval, TimedExecution.eval, PMF.map_bind, PMF.map_bind]
      exact timed_bind code oracle c d h _ (fun c d h => ih c d h)

/-- A cell-invariant postcondition holding on every canonical branch
also holds on every actual branch. Actual finite tapes are never replaced. -/
theorem eval_postcondition {State : Type*} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (actual canonical : Configuration State) (entry : Frames actual canonical)
    (property : Configuration State → Prop)
    (invariant : ∀ c d, Frames c d → (property c ↔ property d))
    (valid : ∀ finish ∈ (Reification.eval code oracle fuel canonical).support, property finish)
    (finish : Configuration State)
    (support : finish ∈ (Reification.eval code oracle fuel actual).support) : property finish := by
  classical
  have law := eval_map code oracle fuel actual canonical entry
    (fun frame => decide (property frame)) (fun c d h => by simp only [invariant c d h])
  have seen : decide (property finish) ∈
      ((Reification.eval code oracle fuel actual).map (fun frame => decide (property frame))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, support, rfl⟩
  rw [law, PMF.mem_support_map_iff] at seen
  obtain ⟨reference, href, he⟩ := seen
  have proved : decide (property reference) = true := by simp [valid reference href]
  exact of_decide_eq_true (he.symm.trans proved)

/-- Actual first-halt times are retained jointly with any cell-invariant
observation. This does not identify the two finite zipper records. -/
theorem first_map {State α : Type*} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (c d : Configuration State) (h : Frames c d)
    (observe : Configuration State × Nat → α)
    (ho : ∀ c d time, Frames c d → observe (c, time) = observe (d, time)) :
    (TimedExecution.runToBoundary (Reification.timedStep code oracle)
      (fun c => Reification.terminal c.control) fuel c).map observe =
    (TimedExecution.runToBoundary (Reification.timedStep code oracle)
      (fun c => Reification.terminal c.control) fuel d).map observe := by
  induction fuel generalizing c d observe with
  | zero => simp [TimedExecution.runToBoundary, PMF.pure_map, ho c d 0 h]
  | succ fuel ih =>
      have ht := terminal h.2.2
      cases hb : Reification.terminal c.control with
      | true => simp [TimedExecution.runToBoundary, ← ht, hb, PMF.pure_map, ho c d 0 h]
      | false =>
          simp only [TimedExecution.runToBoundary, ← ht, hb, Bool.false_eq_true,
            ↓reduceIte, PMF.map_bind, PMF.map_comp, Function.comp_def]
          apply timed_bind code oracle c d h
          intro next other he
          exact ih next other he (fun result => observe (result.1, result.2 + 1))
            (fun first second time he => ho first second (time + 1) he)

/-- Packet, full oracle state and history may all be observed together. -/
def packetObservation {State : Type*} (c : Configuration State) :=
  (Reification.packet c.control, c.state, c.reverseTrace)

theorem packet_eq {State : Type*} (c d : Configuration State) (h : Frames c d) :
    packetObservation c = packetObservation d := by
  rcases c with ⟨state, control, trace⟩
  rcases d with ⟨other, otherControl, otherTrace⟩
  rcases h with ⟨rfl, rfl, h⟩
  cases h with
  | running he => simp [packetObservation, Reification.packet, he.2.1, he.outputBits]
  | _ => rfl

/-- Retain a caller's transcript prefix without exposing it to native code. -/
def appendTrace {State : Type*} (prior : List (List Bool × List Bool))
    (c : Configuration State) : Configuration State :=
  { c with reverseTrace := c.reverseTrace ++ prior }

theorem eval_appendTrace {State : Type*} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (state : State) (control : Control) (prior : List (List Bool × List Bool)) :
    Reification.eval code oracle fuel ⟨state, control, prior⟩ =
      (Reification.eval code oracle fuel ⟨state, control, []⟩).map (appendTrace prior) := by
  rw [← Reification.program_run code oracle fuel ⟨state, control, prior⟩,
    ← Reification.program_run code oracle fuel ⟨state, control, []⟩]
  simp only [PMF.map_comp, Function.comp_def]
  congr 1
  funext out
  simp [appendTrace, Reification.assemble]

end CryptoOracle.Interactive.CellEquivalence

