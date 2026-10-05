import Foundation.Crypto.Semantics.Machine.INDCPAReachability
import Foundation.Examples.BitMachineExecution
import Foundation.Crypto.Semantics.Security.Asymptotic

namespace Machine.Examples

open Foundation.Probability

/-- A minimal two-stage scheme used only to check that the reachable-input
class admits a finite machine program. -/
noncomputable def unitScheme : PKE ProbComp where
  PublicKey := Unit
  SecretKey := Unit
  Message := Unit
  Ciphertext := Unit
  keygen := PMF.pure ((), ())
  encrypt := fun _ _ => PMF.pure ()
  decrypt := fun _ _ => some ()

def unitSemantics : INDCPASemantics ProbComp where
  advantage := fun _ _ _ => 0

def unitRequestCode : FiniteBitEncoding (Unit ⊕ (List Bool × Unit)) where
  encode
    | .inl _ => [false]
    | .inr (state, _) => true :: state
  decode
    | [] => none
    | false :: [] => some (.inl ())
    | false :: _ => none
    | true :: state => some (.inr (state, ()))
  decode_encode := by
    intro request
    cases request with
    | inl value => cases value; rfl
    | inr value => rcases value with ⟨state, u⟩; cases u; rfl

def unitResponseCode : FiniteBitEncoding ((Unit × Unit × List Bool) ⊕ Bool) where
  encode
    | .inl (_, _, state) => false :: state
    | .inr bit => [true, bit]
  decode
    | [] => none
    | false :: state => some (.inl ((), (), state))
    | [true, bit] => some (.inr bit)
    | true :: _ => none
  decode_encode := by
    intro response
    cases response with
    | inl value => rcases value with ⟨m₀, m₁, state⟩; cases m₀; cases m₁; rfl
    | inr bit => cases bit <;> rfl

def unitInstanceCode : FiniteBitEncoding (ULift Unit) where
  encode _ := []
  decode
    | [] => some (ULift.up ())
    | _ => none
  decode_encode := by
    intro x
    rcases x with ⟨u⟩
    cases u
    rfl

noncomputable def unitINDCPAInterface :=
  indCPAReindexedInterface unitSemantics (fun _ => ULift Unit)
    (fun _ _ => unitScheme) (fun _ => unitInstanceCode)
    (fun _ _ => unitRequestCode) (fun _ _ => unitResponseCode)
    (fun _ _ => ())

def unitINDCPAFamily : (n : Nat) → ULift Unit := fun _ => ULift.up ()

theorem unitResponseCode_stateSizeFaithful :
    ChooseStateSizeFaithful (fun _ => ULift Unit) (fun _ _ => unitScheme)
      (fun _ _ => unitResponseCode) := by
  intro n x bits m₀ m₁ state h
  cases bits with
  | nil => simp [unitResponseCode] at h
  | cons tag rest =>
      cases tag with
      | false =>
          simp [unitResponseCode] at h
          cases h
          simp
      | true =>
          cases rest with
          | nil => simp [unitResponseCode] at h
          | cons bit tail =>
              cases tail
              · cases bit <;> simp [unitResponseCode] at h <;> cases h
              · simp [unitResponseCode] at h

theorem unitINDCPA_choose_size (n : Nat) (pk : Unit) :
    (unitINDCPAInterface.machineInput n (ULift.up ()) (.inl pk)).length ≤
      2 * (n + 5) := by
  cases pk
  simp [unitINDCPAInterface, MachineAdversaryInterface.machineInput,
    indCPAReindexedInterface, unitRequestCode, unitInstanceCode,
    encodeSecurityParameter, frame]

theorem unitINDCPA_guess_size (n : Nat) (state : List Bool)
    (ciphertext : Unit) :
    (unitINDCPAInterface.machineInput n (ULift.up ()) (.inr (state, ciphertext))).length ≤
      2 * (n + 5) * (state.length + 1) := by
  cases ciphertext
  simp [unitINDCPAInterface, MachineAdversaryInterface.machineInput,
    indCPAReindexedInterface, unitRequestCode, unitInstanceCode,
    encodeSecurityParameter, frame]
  nlinarith [Nat.zero_le (n * state.length)]

/-- This is a nonempty instance of the reachable-request class. The same
halt program is used at every security parameter and for both stages. -/
theorem haltImmediately_reachableINDCPAPPT :
    (indCPAReindexedReachablePPTClass unitSemantics (fun _ => ULift Unit)
      (fun _ _ => unitScheme) (fun _ => unitInstanceCode)
      (fun _ _ => unitRequestCode) (fun _ _ => unitResponseCode)
      (fun _ _ => ()) unitResponseCode_stateSizeFaithful).admissible unitINDCPAFamily
      (unitINDCPAInterface.realizeFamily unitINDCPAFamily
        haltImmediately (fun _ => 1)) := by
  refine ⟨haltImmediately, (fun _ => 1), (fun n => 2 * (n + 5)),
    PolynomiallyBounded.const 1, haltImmediately_haltsWithin, ?_, ?_, ?_, rfl⟩
  · exact (PolynomiallyBounded.const 2).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 5))
  · intro n pk
    exact unitINDCPA_choose_size n pk
  · intro n state ciphertext
    exact unitINDCPA_guess_size n state ciphertext

example : ∃ inputBound : Nat → Nat, PolynomiallyBounded inputBound ∧
    ∀ n (pk : Unit),
      (unitINDCPAInterface.machineInput n (ULift.up ()) (.inl pk)).length ≤ inputBound n := by
  obtain ⟨_, _, inputBound, hPoly, hChoose, _, _⟩ :=
    indCPAReindexedReachablePPTClass_input_polynomial unitSemantics
      (fun _ => ULift Unit) (fun _ _ => unitScheme)
      (fun _ => unitInstanceCode) (fun _ _ => unitRequestCode)
      (fun _ _ => unitResponseCode) (fun _ _ => ())
      unitResponseCode_stateSizeFaithful unitINDCPAFamily
      (unitINDCPAInterface.realizeFamily unitINDCPAFamily
        haltImmediately (fun _ => 1)) haltImmediately_reachableINDCPAPPT
  exact ⟨inputBound, hPoly, hChoose⟩

/-- The old all-request class is empty even for this toy scheme, while the
reachable-request class has the concrete `haltImmediately` member above. -/
example : ¬ unitINDCPAInterface.pptClass.admissible unitINDCPAFamily
    (unitINDCPAInterface.realizeFamily unitINDCPAFamily
      haltImmediately (fun _ => 1)) := by
  exact indCPAReindexedInterface_pptClass_empty unitSemantics
    (fun _ => ULift Unit) (fun _ _ => unitScheme)
    (fun _ => unitInstanceCode) (fun _ _ => unitRequestCode)
    (fun _ _ => unitResponseCode) (fun _ _ => ())
    unitINDCPAFamily 0 () _

example : SecureOnWithin
    ((INDCPA ProbComp unitSemantics).reindex (fun _ => ULift Unit)
      (fun _ _ => unitScheme))
    (indCPAReindexedReachablePPTClass unitSemantics (fun _ => ULift Unit)
      (fun _ _ => unitScheme) (fun _ => unitInstanceCode)
      (fun _ _ => unitRequestCode) (fun _ _ => unitResponseCode)
      (fun _ _ => ()) unitResponseCode_stateSizeFaithful) unitINDCPAFamily := by
  intro A _
  change Negligible (fun _ => 0)
  exact Negligible.zero

end Machine.Examples
