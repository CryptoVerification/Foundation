import Foundation.Constructions.Symmetric.SecretPrefixMAC
import Foundation.Crypto.Semantics.Oracle.RandomOracleGuessing

/-! The fresh-tag part of the ROM forgery proof. Public queries which contain
 the key remain a separate bad event; no key-hiding bound is assumed here. -/
namespace Foundation.Symmetric.SecretPrefixMAC

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
local instance {κ : Nat} : BEq (Message κ) := instBEqOfDecidableEq

/-- A public hash input enters the keyed domain. This event concerns any
message, rather than only the eventual forgery message. -/
def KeyHit {κ n : Nat} (key : Key κ) (trace : List (Request κ × Tag n)) : Prop :=
  ∃ message response, (.inl (input key message), response) ∈ trace

def requestInput {κ : Nat} (key : Key κ) : Request κ → Message κ
  | .inl message => message
  | .inr message => input key message

/-- Every final hash-table entry has an origin in an actual request or the
initial table; every signing request is retained in the signed-message list. -/
theorem rom_run_sources {κ n : Nat} (key : Key κ) (attack : Attack κ n)
    (table : RandomOracle.Table (Message κ) (Tag n)) (signed : List (Message κ))
    (out : Outcome (Request κ) (Tag n) (Message κ × Tag n)
      (RandomOracle.Table (Message κ) (Tag n) × List (Message κ)))
    (ho : out ∈ (attack.run (oracle RandomOracle.oracle key) (table, signed)).support) :
    (∀ entry ∈ out.state.1,
      entry ∈ out.trace.map (fun e => (requestInput key e.1, e.2)) ++ table) ∧
    (∀ message ∈ signed, message ∈ out.state.2) ∧
    (∀ message response, (.inr message, response) ∈ out.trace → message ∈ out.state.2) := by
  induction attack generalizing table signed out with
  | done result =>
      rw [Program.run, PMF.mem_support_pure_iff] at ho
      subst out
      exact ⟨by simp, fun _ h => h, by simp⟩
  | coin next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at ho
      obtain ⟨bit, _, ho⟩ := ho
      exact ih bit table signed out ho
  | query request next ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at ho
      obtain ⟨answer, ha, ho⟩ := ho
      cases request with
      | inl message =>
          rw [oracle, PMF.mem_support_map_iff] at ha
          obtain ⟨hashAnswer, hh, rfl⟩ := ha
          rw [PMF.mem_support_map_iff] at ho
          obtain ⟨tail, ht, rfl⟩ := ho
          obtain ⟨hs, hk, ht⟩ := ih hashAnswer.2 hashAnswer.1 signed tail ht
          have hstep := RandomOracle.step_entries table message hashAnswer hh
          refine ⟨?_, hk, ?_⟩
          · intro entry hm
            have h := hs entry hm
            simpa only [List.map_cons, requestInput, List.cons_append, List.mem_cons,
              List.mem_append, or_assoc, or_left_comm, or_comm] using
              (List.mem_append.mp h).elim
                (fun h => Or.inl h) (fun h => Or.inr (hstep h))
          · intro m response hm
            exact ht m response (by simpa using hm)
      | inr message =>
          rw [oracle, tag, PMF.mem_support_map_iff] at ha
          obtain ⟨hashAnswer, hh, rfl⟩ := ha
          rw [PMF.mem_support_map_iff] at ho
          obtain ⟨tail, ht, rfl⟩ := ho
          obtain ⟨hs, hk, ht⟩ := ih hashAnswer.2 hashAnswer.1 (message :: signed) tail ht
          have hstep := RandomOracle.step_entries table (input key message) hashAnswer hh
          refine ⟨?_, fun m hm => hk m (List.mem_cons_of_mem _ hm), ?_⟩
          · intro entry hm
            have h := hs entry hm
            simpa only [List.map_cons, requestInput, List.cons_append, List.mem_cons,
              List.mem_append, or_assoc, or_left_comm, or_comm] using
              (List.mem_append.mp h).elim
                (fun h => Or.inl h) (fun h => Or.inr (hstep h))
          · intro m response hm
            rcases List.mem_cons.mp hm with he | hm
            · cases he
              exact hk message (List.mem_cons_self ..)
            · exact ht m response hm

/-- Without a public query in the keyed domain, an unsigned message has a
fresh hash input at the end of the entire adaptive attack. -/
theorem rom_unsigned_fresh {κ n : Nat} (key : Key κ) (attack : Attack κ n)
    (out : Outcome (Request κ) (Tag n) (Message κ × Tag n)
      (RandomOracle.Table (Message κ) (Tag n) × List (Message κ)))
    (ho : out ∈ (attack.run (oracle RandomOracle.oracle key) ([], [])).support)
    (noHit : ¬KeyHit key out.trace) (unsigned : out.result.1 ∉ out.state.2) :
    out.state.1.lookup (input key out.result.1) = none := by
  cases he : out.state.1.lookup (input key out.result.1) with
  | none => rfl
  | some value =>
      obtain ⟨before, after, hs, _⟩ := List.lookup_eq_some_iff.mp he
      have hm : (input key out.result.1, value) ∈ out.state.1 := by rw [hs]; simp
      obtain ⟨sources, _, signed⟩ := rom_run_sources key attack [] [] out ho
      have ht := sources _ hm
      simp only [List.append_nil, List.mem_map] at ht
      obtain ⟨⟨request, response⟩, ht, eq⟩ := ht
      cases request with
      | inl message =>
          have hinput : message = input key out.result.1 := congrArg Prod.fst eq
          subst message
          exact False.elim (noHit ⟨out.result.1, response, ht⟩)
      | inr message =>
          have hinput : input key message = input key out.result.1 := congrArg Prod.fst eq
          have hmessage : message = out.result.1 := by simpa [input] using hinput
          subst message
          exact False.elim (unsigned (signed _ _ ht))

abbrev ROMOutcome (κ n : Nat) :=
  Outcome (Request κ) (Tag n) (Message κ × Tag n)
    (RandomOracle.Table (Message κ) (Tag n) × List (Message κ))

/-- Joint law of the hidden key and the complete adaptive attack outcome. -/
noncomputable def romTranscript {κ n : Nat} (attack : Attack κ n) :
    ProbComp (Key κ × ROMOutcome κ n) :=
  (keygen κ).bind fun key =>
    (attack.run (oracle RandomOracle.oracle key) ([], [])).map fun out => (key, out)

noncomputable def finalCheck {κ n : Nat} (messageLimit : Nat)
    (key : Key κ) (out : ROMOutcome κ n) : ProbComp Bool :=
  (verify RandomOracle.oracle key out.state.1 out.result.1 out.result.2).map fun answer =>
    answer.2 && decide (out.result.1 ∉ out.state.2) &&
      decide (out.result.1.length ≤ messageLimit)

/-- This is an equality with the original MAC experiment, not a second game
whose attack or final verification has been weakened. -/
theorem romGame_transcript {κ n : Nat} (messageLimit : Nat) (attack : Attack κ n) :
    romGame messageLimit attack =
      (romTranscript attack).bind (fun pair => finalCheck messageLimit pair.1 pair.2) := by
  simp only [romGame, game, romTranscript, finalCheck, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext key
  congr 1
  funext out
  congr 1
  funext answer
  congr 2
  by_cases hs : out.result.1 ∈ out.state.2 <;> simp [hs]

/-- Conditional on any reachable transcript with no keyed public query,
verification of an unsigned message succeeds with at most one random-tag guess. -/
theorem finalCheck_no_hit {κ n : Nat} (messageLimit : Nat) (key : Key κ)
    (attack : Attack κ n) (out : ROMOutcome κ n)
    (ho : out ∈ (attack.run (oracle RandomOracle.oracle key) ([], [])).support)
    (noHit : ¬KeyHit key out.trace) :
    eventProb (finalCheck messageLimit key out) (· = true) ≤
      (Fintype.card (Tag n) : ℝ≥0∞)⁻¹ := by
  by_cases unsigned : out.result.1 ∉ out.state.2
  · have hf := rom_unsigned_fresh key attack out ho noHit unsigned
    simp only [finalCheck, verify, tag, RandomOracle.fresh _ _ hf,
      PMF.map_comp, Function.comp_def]
    rw [eventProb_map]
    calc
      _ ≤ eventProb (uniform (Tag n)) (· = out.result.2) := by
        apply eventProb_mono
        intro value hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        exact hv.1.1
      _ = _ := uniform_guess _
  · rw [finalCheck, eventProb_map]
    simp [unsigned, eventProb]

noncomputable def keyHitProbability {κ n : Nat} (attack : Attack κ n) : ℝ≥0∞ :=
  eventProb (romTranscript attack) (fun pair => KeyHit pair.1 pair.2.trace)

/-- The actual MAC forgery probability is at most the actual key-hit
probability plus one tag guess. Bounding the key-hit probability is still
required for the full ROM security theorem. No bound on it is assumed here. -/
theorem success_le_key_hit_add_guess {κ n : Nat} (messageLimit : Nat)
    (attack : Attack κ n) :
    successProbability messageLimit attack ≤ keyHitProbability attack +
      (Fintype.card (Tag n) : ℝ≥0∞)⁻¹ := by
  rw [successProbability, romGame_transcript]
  apply eventProb_bind_le_bad_add
  intro pair hp noHit
  rw [romTranscript, PMF.mem_support_bind_iff] at hp
  obtain ⟨key, _, hp⟩ := hp
  rw [PMF.mem_support_map_iff] at hp
  obtain ⟨out, ho, rfl⟩ := hp
  exact finalCheck_no_hit messageLimit key attack out ho noHit

/-- Nonempty public hash inputs contribute exactly one key candidate each.
Empty inputs and signing requests contribute none. Repeated candidates remain. -/
def publicHeads {κ n : Nat} (trace : List (Request κ × Tag n)) : List (Key κ) :=
  trace.filterMap fun entry => match entry.1 with
    | .inl (key :: _) => some key
    | _ => none

theorem keyHit_iff_mem_publicHeads {κ n : Nat} (key : Key κ)
    (trace : List (Request κ × Tag n)) :
    KeyHit key trace ↔ key ∈ publicHeads trace := by
  simp only [KeyHit, publicHeads, List.mem_filterMap]
  constructor
  · rintro ⟨message, response, hm⟩
    exact ⟨(.inl (input key message), response), hm, rfl⟩
  · rintro ⟨⟨request, response⟩, hm, hk⟩
    cases request with
    | inr message => simp at hk
    | inl message =>
        cases message with
        | nil => simp at hk
        | cons head tail =>
            simp only [Option.some.injEq] at hk
            subst head
            exact ⟨tail, response, hm⟩

theorem publicHeads_length {κ n : Nat} (trace : List (Request κ × Tag n)) :
    (publicHeads trace).length ≤ trace.countP (fun e => e.1.isLeft) := by
  induction trace with
  | nil => simp [publicHeads]
  | cons entry tail ih =>
      obtain ⟨request, response⟩ := entry
      cases request with
      | inr message => simpa [publicHeads] using ih
      | inl message =>
          cases message with
          | nil => simpa [publicHeads] using (Nat.le_succ_of_le ih)
          | cons head rest => simpa [publicHeads] using (Nat.succ_le_succ ih)

/-- If the entire interaction is independent of the hidden key, qH public
hash queries hit its keyed domain with probability at most qH/card(Key).
This lemma must not be applied directly to the actual ROM MAC oracle: its
signing replies use the key. An experiment comparison is still necessary. -/
theorem independent_key_hit_bound {κ n hashLength messageLength qH qT : Nat}
    {State : Type} (handler : Oracle (Request κ) (Tag n) State) (initial : State)
    (attack : Attack κ n) (budget : Budget hashLength messageLength attack qH qT) :
    eventProb ((attack.run handler initial).bind fun out =>
      (keygen κ).map (fun key => (key, out.trace)))
      (fun pair => KeyHit pair.1 pair.2) ≤
        qH * (Fintype.card (Key κ) : ℝ≥0∞)⁻¹ := by
  apply eventProb_bind_le_of_support
  intro out ho
  rw [eventProb_map]
  simp_rw [keyHit_iff_mem_publicHeads]
  calc
    _ ≤ (publicHeads out.trace).length * (Fintype.card (Key κ) : ℝ≥0∞)⁻¹ :=
      uniform_mem_list _
    _ ≤ _ := mul_le_mul' (by
      exact_mod_cast (publicHeads_length out.trace).trans
        (budget.trace_counts handler initial out ho).1) (le_refl _)

/-- Intermediate experiment: public hashing and tagging use disjoint random
function domains. Both remain consistent on repeated inputs. The hidden key
is independent of the complete attack transcript in this experiment. -/
noncomputable def separatedKeyHitProbability {κ n : Nat} (attack : Attack κ n) : ℝ≥0∞ :=
  eventProb ((attack.run RandomOracle.oracle []).bind fun out =>
    (keygen κ).map (fun key => (key, out.trace)))
    (fun pair => KeyHit pair.1 pair.2)

theorem separated_key_hit_bound {κ n hashLength messageLength qH qT : Nat}
    (attack : Attack κ n) (budget : Budget hashLength messageLength attack qH qT) :
    separatedKeyHitProbability attack ≤ qH * (Fintype.card (Key κ) : ℝ≥0∞)⁻¹ :=
  independent_key_hit_bound RandomOracle.oracle [] attack budget

end Foundation.Symmetric.SecretPrefixMAC
