import Foundation.Quantum.QKD.SeededCQ
import Foundation.Quantum.QKD.ClassicalBranching
import Foundation.Quantum.QKD.BB84Finalization

/-! Exact accepted/abort decomposition of the actual randomized BB84 hashed
output. Correctness and secrecy premises remain proof obligations for the
actual accepted branch; they are not axioms about arbitrary attacks. -/
namespace Foundation.Quantum.QKD.FinalSecurity
noncomputable section
open Subnormalized AcceptedAbort
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
variable {n length : Nat} {S : Type} [Fintype S] [DecidableEq S] {e : Space}

abbrev SourceLabel (n : Nat) (S : Type) := S × Fin (Fintype.card (RawProtocol.Output n))

def source (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S) : State (SourceLabel n S) e :=
  ofCQ (SeededCQ.independent p (Guessing.bb84Blocks A k minKey tolerance))

def raw (sr : SourceLabel n S) : RawProtocol.Output n := (Fintype.equivFin _).symm sr.2

def accepts (sr : SourceLabel n S) : Prop := (raw sr).transcript.accepted = true
instance : DecidablePred (accepts (n := n) (S := S)) := fun sr => inferInstanceAs (Decidable ((raw sr).transcript.accepted = true))

def publicFields (sr : SourceLabel n S) : Finalization.Transcript n S := ((raw sr).transcript,sr.1)

def acceptedFields (hash : S → Finalization.RawKey n → IdealKey.Key length) (sr : SourceLabel n S) :
    AcceptedLabel (Finalization.Transcript n S) length :=
  ((hash sr.1 (raw sr).aliceKey,hash sr.1 (raw sr).bobKey),publicFields sr)

def acceptedBranch (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    State (AcceptedLabel (Finalization.Transcript n S) length) e :=
  relabel (restrict (source A k minKey tolerance p) accepts) (acceptedFields hash)

def abortBranch (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S) :
    State (Finalization.Transcript n S) e :=
  relabel (restrict (source A k minKey tolerance p) (fun sr => ¬ accepts sr)) publicFields

theorem branch_mass (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    mass (acceptedBranch A k minKey tolerance p hash) + mass (abortBranch A k minKey tolerance p) = 1 := by
  unfold acceptedBranch abortBranch
  rw [ClassicalBranching.final_mass, source, mass_ofCQ]

omit [Fintype S] [DecidableEq S] in
/-- The old Finalization.output is the same explicit classical branch function. -/
theorem output_partition (hash : S → Finalization.RawKey n → IdealKey.Key length) (sr : SourceLabel n S) :
    Finalization.output sr.1 hash (raw sr) =
      if accepts sr then acceptLabel (acceptedFields hash sr) else abortLabel (publicFields sr) := by
  by_cases h : accepts sr
  · have ht : (raw sr).transcript.accepted = true := h
    simp [h, Finalization.output, acceptLabel, acceptedFields, publicFields, ht]
  · have ht : (raw sr).transcript.accepted = false := by
      unfold accepts at h
      cases hh : (raw sr).transcript.accepted <;> simp_all
    simp [h, Finalization.output, abortLabel, publicFields, ht]

/-- The actual old output density equals the constructed accepted/abort
state, retaining public seed, transcript, both private keys and Eve. -/
theorem state_partition (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    (Finalization.state A k minKey tolerance p hash).matrix =
      (AcceptedAbort.state (acceptedBranch A k minKey tolerance p hash)
        (abortBranch A k minKey tolerance p) (branch_mass A k minKey tolerance p hash)).matrix := by
  have hp := SeededCQ.physical p (Randomized.keyState A k minKey tolerance)
    (fun sr : SourceLabel n S => Finalization.output sr.1 hash (raw sr))
  change joint (relabel (source A k minKey tolerance p) (fun sr => Finalization.output sr.1 hash (raw sr))) =
    (Finalization.state A k minKey tolerance p hash).matrix at hp
  rw [← hp]
  simp_rw [output_partition]
  rw [ClassicalBranching.final_partition]
  rfl

theorem state_eq (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    Finalization.state A k minKey tolerance p hash =
      AcceptedAbort.state (acceptedBranch A k minKey tolerance p hash)
        (abortBranch A k minKey tolerance p) (branch_mass A k minKey tolerance p hash) := by
  have hmEq := state_partition A k minKey tolerance p hash
  cases hρ : Finalization.state A k minKey tolerance p hash
  cases hσ : AcceptedAbort.state (acceptedBranch A k minKey tolerance p hash)
    (abortBranch A k minKey tolerance p) (branch_mass A k minKey tolerance p hash)
  rw [hρ, hσ] at hmEq
  cases hmEq
  rfl

/-- The correctness premise is the actual full protocol mismatch probability. -/
theorem correctness_probability (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    (recordEvent e (fun r => let o : IdealKey.Output (Finalization.Transcript n S) length := (Fintype.equivFin _).symm r
      o.aliceKey ≠ o.bobKey)).probability (Finalization.state A k minKey tolerance p hash) =
        CommonKey.correctnessError (acceptedBranch A k minKey tolerance p hash) := by
  rw [state_eq]
  exact AcceptedAbort.correctness_probability _ _ _

/-- The accepted branch mass is the physical acceptance probability in the
actual final state, independent of the deterministic hash used for its keys. -/
theorem acceptance_probability (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    (recordEvent e (fun r => let o : IdealKey.Output (Finalization.Transcript n S) length := (Fintype.equivFin _).symm r
      o.accepted = true)).probability (Finalization.state A k minKey tolerance p hash) =
        mass (acceptedBranch A k minKey tolerance p hash) := by
  rw [state_eq]
  unfold Effect.probability AcceptedAbort.state
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rw [relabel_event_observation (ρ := acceptedBranch A k minKey tolerance p hash)
      (f := acceptLabel) (P := fun o => o.accepted = true),
    relabel_event_observation (ρ := abortBranch A k minKey tolerance p)
      (f := abortLabel) (P := fun o => o.accepted = true)]
  simp only [acceptLabel, abortLabel, Bool.false_eq_true, ite_true, ite_false,
    Finset.sum_const_zero, add_zero, mass]

/-- Interpret the two-step finite derivation on the actual BB84 branches,
then use their proved equality with the existing final protocol state. -/
theorem secure (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) (δ ε : ℝ)
    (hc : CommonKey.correctnessError (acceptedBranch A k minKey tolerance p hash) ≤ δ)
    (hs : OperatorApprox (joint (CommonKey.aliceView (acceptedBranch A k minKey tolerance p hash)))
      (joint (CommonKey.uniformize (CommonKey.aliceView (acceptedBranch A k minKey tolerance p hash)))) ε) :
    IdealKey.Secure (Finalization.state A k minKey tolerance p hash) (δ+ε) := by
  let ρ := acceptedBranch A k minKey tolerance p hash
  let σ := abortBranch A k minKey tolerance p
  let hm := branch_mass A k minKey tolerance p hash
  have h : IdealKey.Secure (AcceptedAbort.state ρ σ hm) (δ+ε) := by
    apply AcceptedAbortLogic.sound (fun _ => ρ) (fun _ => σ) (fun _ => hm)
      (AcceptedAbortLogic.proof 0 δ ε)
    intro i
    change Fin 2 at i
    by_cases hi : i = 0
    · subst i
      exact hc
    · have hi1 : i = 1 := by omega
      subst i
      exact hs
  rw [state_eq]
  exact h

end
end Foundation.Quantum.QKD.FinalSecurity
