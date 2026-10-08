import Foundation.Constructions.Symmetric.PRF
import Foundation.Crypto.Semantics.Security.ThreeGames

/-! Stateful counter encryption and its typed adaptive PRF simulator.
This module proves semantic simulation and query bounds. Program continuations
are analysis syntax. PRFCounterResource connects represented source programs
to the separately implemented finite CPU compiler and its resource certificates. -/
namespace Foundation.Symmetric.PRFCounter

open Foundation.Probability CryptoOracle
set_option backward.isDefEq.respectTransparency false

abbrev Request (length : Nat) := Bits length × Bits length
abbrev Response (length : Nat) := Option (Nat × Bits length)
abbrev Attack (length : Nat) := Program (Request length) (Response length) Bool

def selected {length : Nat} (right : Bool) (request : Request length) : Bits length :=
  if right then request.2 else request.1

def encrypt {capacity length : Nat} (table : Fin capacity → Bits length)
    (counter : Fin capacity) (message : Bits length) : Nat × Bits length :=
  (counter.val, Bits.xor (table counter) message)

def decrypt {capacity length : Nat} (table : Fin capacity → Bits length)
    (counter : Fin capacity) (ciphertext : Bits length) : Bits length :=
  Bits.xor (table counter) ciphertext

@[simp] theorem correctness {capacity length : Nat} (table : Fin capacity → Bits length)
    (counter : Fin capacity) (message : Bits length) :
    decrypt table counter (encrypt table counter message).2 = message :=
  Bits.xor_self_cancel _ _

/-- Ciphertexts expose a natural-number counter. Invalid counters are
rejected before constructing a finite-domain PRF input. -/
def decryptCiphertext {capacity length : Nat} (table : Fin capacity → Bits length)
    (ciphertext : Nat × Bits length) : Option (Bits length) :=
  if h : ciphertext.1 < capacity then
    some (decrypt table ⟨ciphertext.1, h⟩ ciphertext.2)
  else none

def decryptResponse {capacity length : Nat} (table : Fin capacity → Bits length)
    (response : Response length) : Option (Bits length) :=
  response.bind (decryptCiphertext table)

@[simp] theorem decryptCiphertext_encrypt {capacity length : Nat}
    (table : Fin capacity → Bits length) (counter : Fin capacity) (message : Bits length) :
    decryptCiphertext table (encrypt table counter message) = some message := by
  simp only [decryptCiphertext, encrypt, decrypt, counter.isLt, dite_true, Bits.xor_self_cancel]

/-- Exhaustion returns no ciphertext and never reuses an earlier counter. -/
noncomputable def oracle {capacity length : Nat} (table : Fin capacity → Bits length)
    (right : Bool) : Oracle (Request length) (Response length) Nat :=
  fun counter request =>
    if h : counter < capacity then
      PMF.pure (counter + 1, some (encrypt table ⟨counter, h⟩ (selected right request)))
    else PMF.pure (counter, none)

/-- Decryption is correct for every successful oracle response, and
capacity exhaustion remains an explicit failure. -/
theorem oracle_correctness {capacity length : Nat} (table : Fin capacity → Bits length)
    (right : Bool) (counter : Nat) (request : Request length) :
    (oracle table right counter request).map (fun response => decryptResponse table response.2) =
      PMF.pure (if counter < capacity then some (selected right request) else none) := by
  by_cases h : counter < capacity <;> simp [oracle, h, decryptResponse, PMF.pure_map]

/-- Typed simulator: one PRF request per successful encryption. CounterMasking
implements the local counter and plaintext masking with finite code;
PRFCounterResource proves its connection for represented source attacks. -/
def reduce {capacity length : Nat} (right : Bool) : Nat → Attack length →
    Program (Fin capacity) (Bits length) Bool
  | _, .done result => .done result
  | counter, .query request next =>
      if h : counter < capacity then
        .query ⟨counter, h⟩ (fun pad => reduce right (counter + 1)
          (next (some (counter, Bits.xor pad (selected right request)))))
      else reduce right counter (next none)
  | counter, .coin next => .coin (fun bit => reduce right counter (next bit))

/-- The same adaptive ciphertext observations are delivered to the attack.
The equality concerns its output, not private state or the PRF transcript. -/
theorem simulation {capacity length : Nat} (table : Fin capacity → Bits length)
    (right : Bool) (counter : Nat) (attack : Attack length) :
    ((reduce (capacity := capacity) right counter attack).run (PRF.tableOracle table) ()).map
        Outcome.result =
      (attack.run (oracle table right) counter).map Outcome.result := by
  induction attack generalizing counter with
  | done result => simp [reduce, Program.run, PMF.pure_map]
  | query request next ih =>
      by_cases h : counter < capacity
      · simp only [reduce, h, dite_true, Program.run, oracle, PRF.tableOracle, PMF.pure_bind,
          PMF.map_comp, Function.comp_def]
        exact ih _ (counter + 1)
      · simp only [reduce, h, dite_false, Program.run, oracle, PMF.pure_bind,
          PMF.map_comp, Function.comp_def]
        exact ih none counter
  | coin next ih =>
      simp only [reduce, Program.run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit counter

/-- The simulator cannot increase the worst-case number of queries. -/
theorem queries {capacity length : Nat} (right : Bool) (counter : Nat)
    (attack : Attack length) (q : Nat) (h : attack.BoundedQueries q) :
    (reduce (capacity := capacity) right counter attack).BoundedQueries q := by
  induction h generalizing counter with
  | done result q => exact .done _ _
  | query request next q h ih =>
      by_cases hc : counter < capacity
      · simp only [reduce, hc, dite_true]
        exact .query _ _ _ (fun pad => ih _ (counter + 1))
      · simp only [reduce, hc, dite_false]
        exact (ih none counter).mono (by omega)
  | coin next q h ih => exact .coin _ _ (fun bit => ih bit counter)


structure Scheme where
  Key : Nat → Type
  capacity : Nat → Nat
  length : Nat → Nat
  keygen : ∀ n, ProbComp (Key n)
  evaluate : ∀ n, Key n → Fin (capacity n) → Bits (length n)

def Scheme.toPRF (S : Scheme) : PRF.Scheme where
  Key := S.Key
  Domain := fun n => Fin (S.capacity n)
  domainFinite := fun _ => inferInstance
  length := S.length
  keygen := S.keygen
  evaluate := S.evaluate

noncomputable def runTable {capacity length : Nat} (attack : Attack length)
    (right : Bool) (table : Fin capacity → Bits length) : ProbComp Bool :=
  (attack.run (oracle table right) 0).map Outcome.result

noncomputable def real (S : Scheme) (n : Nat) (right : Bool)
    (attack : Attack (S.length n)) : ProbComp Bool :=
  (S.keygen n).bind fun key => runTable attack right (S.evaluate n key)

noncomputable def ideal (S : Scheme) (n : Nat) (right : Bool)
    (attack : Attack (S.length n)) : ProbComp Bool := by
  classical
  letI := S.toPRF.domainFinite n
  exact (uniform (S.toPRF.Domain n → Bits (S.toPRF.length n))).bind (runTable attack right)

theorem real_simulation (S : Scheme) (n : Nat) (right : Bool)
    (attack : Attack (S.length n)) :
    PRF.real S.toPRF n (reduce right 0 attack) = real S n right attack := by
  unfold PRF.real real
  congr 1
  funext key
  exact simulation (S.evaluate n key) right 0 attack

theorem ideal_simulation (S : Scheme) (n : Nat) (right : Bool)
    (attack : Attack (S.length n)) :
    PRF.ideal S.toPRF n (reduce right 0 attack) = ideal S n right attack := by
  unfold PRF.ideal ideal
  congr 1
  funext table
  exact simulation table right 0 attack

/-- Both PRF gaps and the remaining ideal-encryption gap are explicit.
Perfect ideal privacy, and the CPU compiler, are separate obligations. -/
theorem advantage_bound (S : Scheme) (n : Nat) (attack : Attack (S.length n)) :
    probabilityGap (eventProb (real S n false attack) (· = true))
      (eventProb (real S n true attack) (· = true)) ≤
    (PRF.goal S.toPRF).advantage n () (reduce false 0 attack) +
      probabilityGap (eventProb (ideal S n false attack) (· = true))
        (eventProb (ideal S n true attack) (· = true)) +
      (PRF.goal S.toPRF).advantage n () (reduce true 0 attack) := by
  have hl := CryptoLogic.ThreeGames.probabilityGap_triangle
    (eventProb (real S n false attack) (· = true))
    (eventProb (ideal S n false attack) (· = true))
    (eventProb (ideal S n true attack) (· = true))
  have hr := CryptoLogic.ThreeGames.probabilityGap_triangle
    (eventProb (real S n false attack) (· = true))
    (eventProb (ideal S n true attack) (· = true))
    (eventProb (real S n true attack) (· = true))
  have h := hr.trans (add_le_add hl (le_refl _))
  change probabilityGap _ _ ≤ probabilityGap _ _ + probabilityGap _ _ + probabilityGap _ _
  rw [real_simulation, ideal_simulation, real_simulation, ideal_simulation]
  simpa only [probabilityGap, max_comm] using h

end Foundation.Symmetric.PRFCounter
