import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityLocalExecution

/-! One request's actual encryption, signing and return. A response-length
contract is supplied by the concrete signing oracle, not by the CPU syntax.
Failures leave the signing state and entire signing history unchanged. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
  (key : Bool) (machine : Configuration) (request : List Bool) (state : State)
  (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool))

def signedResult (key : Bool) (machine : Configuration) (request : List Bool)
    (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool))
    (answer : State × List Bool) : Frame State :=
  let ciphertext := Bool.xor key (request.headD false)
  resumed key machine request (true :: ciphertext :: answer.2) answer.1 sourceTrace
    ((ciphertext, answer.2) :: signingTrace)

theorem successful_query_run (width : Nat)
    (hTags : ∀ answer ∈ (oracle state (Bool.xor key (request.headD false))).support, answer.2.length = width) :
    eval code oracle (5 * width + 35)
      ⟨state, .encrypting key false machine request IntegrityPreparation.initial, sourceTrace, signingTrace⟩ =
      (oracle state (Bool.xor key (request.headD false))).map
        (signedResult key machine request sourceTrace signingTrace) := by
  rw [show 5 * width + 35 = encryptionBudget false + ((5 * width + 14) + 1) by
      simp [encryptionBudget, IntegrityEncryption.steps]; omega,
    eval_add, local_encryption_run, PMF.pure_bind, eval_succ]
  have hStep : step code oracle (encrypted key false machine request state sourceTrace signingTrace) =
      (oracle state (Bool.xor key (request.headD false))).map (fun answer =>
        ⟨answer.1, .header key machine request (Bool.xor key (request.headD false)) answer.2 0 {},
          sourceTrace, (Bool.xor key (request.headD false), answer.2) :: signingTrace⟩) := rfl
  rw [hStep, PMF.bind_map]
  change (oracle state (Bool.xor key (request.headD false))).bind (fun answer =>
    eval code oracle (5 * width + 14)
      ⟨answer.1, .header key machine request (Bool.xor key (request.headD false)) answer.2 0 {},
        sourceTrace, (Bool.xor key (request.headD false), answer.2) :: signingTrace⟩) = _
  rw [PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext answer hAnswer
  rw [← hTags answer hAnswer, signed_response_run]
  rfl

def queryBudget (used : Bool) (width : Nat) : Nat := if used then 21 else 5 * width + 35

noncomputable def queryResult (used key : Bool) (machine : Configuration) (request : List Bool)
    (state : State) (sourceTrace : List (List Bool × List Bool))
    (signingTrace : List (Bool × List Bool)) (oracle : State → Bool → PMF (State × List Bool)) : PMF (Frame State) :=
  if used then PMF.pure (resumed key machine request [false] state sourceTrace signingTrace)
  else (oracle state (Bool.xor key (request.headD false))).map
    (signedResult key machine request sourceTrace signingTrace)

theorem query_run (used : Bool) (width : Nat)
    (hTags : ∀ answer ∈ (oracle state (Bool.xor key (request.headD false))).support, answer.2.length = width) :
    eval code oracle (queryBudget used width)
      ⟨state, .encrypting key used machine request IntegrityPreparation.initial, sourceTrace, signingTrace⟩ =
      queryResult used key machine request state sourceTrace signingTrace oracle := by
  cases used with
  | false => exact successful_query_run code oracle key machine request state sourceTrace signingTrace width hTags
  | true => exact failed_query_run code oracle key machine request state sourceTrace signingTrace

noncomputable def queryBlock (used : Bool) (width : Nat) :
    TimedExecution.Block (step code oracle)
      ⟨state, .encrypting key used machine request IntegrityPreparation.initial, sourceTrace, signingTrace⟩ :=
  TimedExecution.Block.fixed (step code oracle) (queryBudget used width) _

theorem queryBlock_outcome (used : Bool) (width : Nat)
    (hTags : ∀ answer ∈ (oracle state (Bool.xor key (request.headD false))).support, answer.2.length = width) :
    (queryBlock code oracle key machine request state sourceTrace signingTrace used width).outcome =
      (queryResult used key machine request state sourceTrace signingTrace oracle).map
        (fun frame => (frame, queryBudget used width)) := by
  change (eval code oracle (queryBudget used width)
    ⟨state, .encrypting key used machine request IntegrityPreparation.initial, sourceTrace, signingTrace⟩).map _ = _
  rw [query_run code oracle key machine request state sourceTrace signingTrace used width hTags]

theorem queryBudget_le (used : Bool) (width : Nat) : queryBudget used width ≤ 5 * width + 35 := by
  cases used <;> simp [queryBudget]

theorem queryResult_source (used : Bool) (frame : Frame State)
    (h : frame ∈ (queryResult used key machine request state sourceTrace signingTrace oracle).support) :
    sourceBoundary frame = true := by
  cases used with
  | true =>
      simp only [queryResult, ↓reduceIte, PMF.mem_support_pure_iff] at h
      subst frame
      rfl
  | false =>
      simp only [queryResult, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
      obtain ⟨answer, _, hFrame⟩ := h
      subst frame
      rfl

theorem queryBlock_completes (used : Bool) (width : Nat)
    (hTags : ∀ answer ∈ (oracle state (Bool.xor key (request.headD false))).support, answer.2.length = width) :
    (queryBlock code oracle key machine request state sourceTrace signingTrace used width).Completes sourceBoundary := by
  intro result hResult
  rw [queryBlock_outcome code oracle key machine request state sourceTrace signingTrace used width hTags,
    PMF.mem_support_map_iff] at hResult
  obtain ⟨frame, hFrame, hResult⟩ := hResult
  subst result
  exact queryResult_source oracle key machine request state sourceTrace signingTrace used frame hFrame

/-- Includes the source's actual pending oracle-call transition. -/
theorem awaiting_query_run (used : Bool) (width : Nat)
    (hTags : ∀ answer ∈ (oracle state (Bool.xor key (request.headD false))).support, answer.2.length = width) :
    eval code oracle (queryBudget used width + 1)
      ⟨state, .source key used (.awaiting machine request), sourceTrace, signingTrace⟩ =
      queryResult used key machine request state sourceTrace signingTrace oracle := by
  rw [eval_succ]
  have hStep : step code oracle
      ⟨state, .source key used (.awaiting machine request), sourceTrace, signingTrace⟩ =
        PMF.pure ⟨state, .encrypting key used machine request IntegrityPreparation.initial, sourceTrace, signingTrace⟩ := rfl
  rw [hStep, PMF.pure_bind, query_run code oracle key machine request state sourceTrace signingTrace used width hTags]

noncomputable def awaitingQueryBlock (used : Bool) (width : Nat) :
    TimedExecution.Block (step code oracle)
      ⟨state, .source key used (.awaiting machine request), sourceTrace, signingTrace⟩ :=
  TimedExecution.Block.fixed (step code oracle) (queryBudget used width + 1) _

theorem awaitingQueryBlock_outcome (used : Bool) (width : Nat)
    (hTags : ∀ answer ∈ (oracle state (Bool.xor key (request.headD false))).support, answer.2.length = width) :
    (awaitingQueryBlock code oracle key machine request state sourceTrace signingTrace used width).outcome =
      (queryResult used key machine request state sourceTrace signingTrace oracle).map
        (fun frame => (frame, queryBudget used width + 1)) := by
  change (eval code oracle (queryBudget used width + 1)
    ⟨state, .source key used (.awaiting machine request), sourceTrace, signingTrace⟩).map _ = _
  rw [awaiting_query_run code oracle key machine request state sourceTrace signingTrace used width hTags]

theorem awaitingQueryBlock_budget (used : Bool) (width : Nat) :
    (awaitingQueryBlock code oracle key machine request state sourceTrace signingTrace used width).budget ≤
      5 * width + 36 := by
  change queryBudget used width + 1 ≤ 5 * width + 36
  have h := queryBudget_le used width
  omega

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
