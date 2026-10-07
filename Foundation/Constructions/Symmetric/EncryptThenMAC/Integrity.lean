import Foundation.Constructions.Symmetric.EncryptThenMAC.Semantics

/-! Ciphertext integrity reduces to strong MAC unforgeability: the entire
ciphertext/tag pair must be fresh, including for an already signed message.
The simulator maintains encryption state and never signs a failed response. -/
namespace Foundation.Symmetric.EncryptThenMAC

open Foundation.Probability CryptoOracle
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable (E : Encryption) (M : MAC E.Ciphertext)

abbrev IntegrityAttack (n : Nat) :=
  Program (E.Message n) (Option (AuthCiphertext E M n)) (AuthCiphertext E M n)
abbrev MACAttack (n : Nat) :=
  Program (E.Ciphertext n) (M.Tag n) (AuthCiphertext E M n)

noncomputable def integrityOracle (n : Nat) (key : E.Key n) (macKey : M.Key n) :
    Oracle (E.Message n) (Option (AuthCiphertext E M n)) (E.State n) :=
  fun state request => let response := E.encrypt n key state request
    PMF.pure (response.1, authenticate E M n macKey response.2)

noncomputable def signingOracle (n : Nat) (macKey : M.Key n) :
    Oracle (E.Ciphertext n) (M.Tag n) Unit :=
  fun _ request => PMF.pure ((), M.sign n macKey request)

def reduceIntegrity {n : Nat} (key : E.Key n) :
    E.State n → IntegrityAttack E M n → MACAttack E M n
  | _, .done forgery => .done forgery
  | state, .query message next =>
      let response := E.encrypt n key state message
      match response.2 with
      | none => reduceIntegrity key response.1 (next none)
      | some ciphertext => .query ciphertext (fun tag =>
          reduceIntegrity key response.1 (next (some (ciphertext, tag))))
  | state, .coin next => .coin (fun bit => reduceIntegrity key state (next bit))

def integrityRecord {n : Nat}
    (out : Outcome (E.Message n) (Option (AuthCiphertext E M n))
      (AuthCiphertext E M n) (E.State n)) :
    AuthCiphertext E M n × List (AuthCiphertext E M n) :=
  (out.result, out.trace.filterMap (fun entry => entry.2))

def signingRecord {n : Nat}
    (out : Outcome (E.Ciphertext n) (M.Tag n) (AuthCiphertext E M n) Unit) :
    AuthCiphertext E M n × List (AuthCiphertext E M n) := (out.result, out.trace)

/-- Joint equality of the final candidate and every signed pair. This is
stronger than equality of the returned candidate alone. -/
theorem integrity_simulation {n : Nat} (key : E.Key n) (macKey : M.Key n)
    (state : E.State n) (attack : IntegrityAttack E M n) :
    ((reduceIntegrity E M key state attack).run (signingOracle E M n macKey) ()).map
      (signingRecord E M) =
    (attack.run (integrityOracle E M n key macKey) state).map (integrityRecord E M) := by
  induction attack generalizing state with
  | done forgery => simp [reduceIntegrity, Program.run, signingRecord, integrityRecord, PMF.pure_map]
  | query message next ih =>
      cases h : E.encrypt n key state message with
      | mk nextState response =>
          cases response with
          | none =>
              have hi := ih none nextState
              change _ = ((next none).run (integrityOracle E M n key macKey) nextState).map
                (fun out => (out.result, out.trace.filterMap (fun entry => entry.2))) at hi
              simpa [reduceIntegrity, integrityOracle, h, Program.run, authenticate,
                integrityRecord, PMF.map_comp, Function.comp_def] using hi
          | some ciphertext =>
              have hi := congrArg
                (fun p : ProbComp (AuthCiphertext E M n × List (AuthCiphertext E M n)) =>
                  p.map (fun pair => (pair.1, (ciphertext, M.sign n macKey ciphertext) :: pair.2)))
                (ih (some (ciphertext, M.sign n macKey ciphertext)) nextState)
              simpa [reduceIntegrity, integrityOracle, signingOracle, h, Program.run, authenticate,
                integrityRecord, signingRecord, PMF.map_comp, Function.comp_def] using hi
  | coin next ih =>
      simp only [reduceIntegrity, Program.run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit state

/-- Failed encryptions cost no signing query. The simulator's query bound is
therefore no greater than the source attack's bound. This is not a CPU bound. -/
theorem integrity_queries {n : Nat} {attack : IntegrityAttack E M n} {q : Nat}
    (h : attack.BoundedQueries q) (key : E.Key n) (state : E.State n) :
    (reduceIntegrity E M key state attack).BoundedQueries q := by
  induction h generalizing state with
  | done result q => exact .done _ _
  | query message next q h ih =>
      cases he : E.encrypt n key state message with
      | mk nextState response =>
          cases response with
          | none =>
              simpa only [reduceIntegrity, he] using (ih none nextState).mono (Nat.le_succ q)
          | some ciphertext =>
              simpa only [reduceIntegrity, he] using
                Program.BoundedQueries.query ciphertext
                  (fun tag => reduceIntegrity E M key nextState (next (some (ciphertext, tag))))
                  q (fun tag => ih _ nextState)
  | coin next q h ih => exact .coin _ q (fun bit => ih bit state)

/-- Strong unforgeability excludes all previously returned pairs. It does
not merely require the ciphertext message to be new. -/
def macWins {n : Nat} (macKey : M.Key n)
    (record : AuthCiphertext E M n × List (AuthCiphertext E M n)) : Prop :=
  M.verify n macKey record.1.1 record.1.2 = true ∧ record.1 ∉ record.2

def integrityWins {n : Nat} (key : E.Key n) (macKey : M.Key n)
    (record : AuthCiphertext E M n × List (AuthCiphertext E M n)) : Prop :=
  (decrypt E M n key macKey record.1).isSome = true ∧ record.1 ∉ record.2

theorem integrityWins_implies_macWins {n : Nat} (key : E.Key n) (macKey : M.Key n)
    (record : AuthCiphertext E M n × List (AuthCiphertext E M n))
    (h : integrityWins E M key macKey record) : macWins E M macKey record := by
  refine ⟨?_, h.2⟩
  by_cases hv : M.verify n macKey record.1.1 record.1.2 = true
  · exact hv
  · have hs := h.1
    simp [decrypt, hv] at hs

end Foundation.Symmetric.EncryptThenMAC
