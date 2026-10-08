import Foundation.Crypto.Semantics.Oracle.InteractiveMachine

/-! Finite code wraps an unchanged interactive attack. Its controller selects
interleaved plaintext cells, copies a unary counter, makes one PRF call,
XORs one pad cell at a time, and resumes the original response loader.
Counters and capacity are tape data, not parameter-dependent code. -/
namespace CryptoOracle.CounterMasking
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

structure Code where
  side : Bool
  program : Interactive.Code
  deriving DecidableEq, Repr, Encodable

def compile (side : Bool) (program : Interactive.Code) : Code := ⟨side, program⟩

inductive Phase where
  | source
  | select : List Bool → List Bool → Phase
  | reverseMask : List Bool → List Bool → Phase
  | copyCounter : List Bool → List Bool → List Bool → Phase
  | awaiting : List Bool → List Bool → Phase
  | masking : List Bool → List Bool → List Bool → Phase
  | reverseCipher : List Bool → List Bool → Phase
  | prependCounter : List Bool → List Bool → Phase
  | deliver : Bool → List Bool → Phase
  deriving DecidableEq, Repr

structure Configuration where
  source : Interactive.Configuration Unit
  capacity : List Bool
  counter : List Bool := []
  phase : Phase := .source
  reverseTrace : List (List Bool × List Bool) := []

/-- The source input and public capacity cells are experiment inputs.
The controller accesses capacity by consuming one cell per successful call. -/
def initial (input capacity : List Bool) : Configuration :=
  ⟨Interactive.Configuration.initial () input, capacity, [], .source, []⟩

inductive Transition where
  | deterministic : Configuration → Transition
  | random : Configuration → Configuration → Transition
  | oracleCall : Configuration → List Bool → List Bool → Transition

/-- Every deterministic controller transition consumes or inserts at most
a fixed number of cells. No host continuation is part of the code. -/
def transition (code : Code) (c : Configuration) : Transition :=
  match c.phase with
  | .source =>
      match Interactive.transition code.program c.source with
      | .deterministic source => .deterministic { c with source := source }
      | .random zero one => .random { c with source := zero } { c with source := one }
      | .oracleCall _ request =>
          match c.capacity with
          | [] => .deterministic { c with phase := .deliver false [false] }
          | _ :: rest => .deterministic { c with capacity := rest, phase := .select request [] }
  | .select (left :: right :: rest) acc =>
      .deterministic { c with phase := .select rest ((if code.side then right else left) :: acc) }
  | .select _ acc => .deterministic { c with phase := .reverseMask acc [] }
  | .reverseMask (bit :: rest) acc =>
      .deterministic { c with phase := .reverseMask rest (bit :: acc) }
  | .reverseMask [] mask =>
      .deterministic { c with phase := .copyCounter c.counter [false] mask }
  | .copyCounter (bit :: rest) acc mask =>
      .deterministic { c with phase := .copyCounter rest (bit :: acc) mask }
  | .copyCounter [] request mask => .deterministic { c with phase := .awaiting request mask }
  | .awaiting request mask => .oracleCall c request mask
  | .masking (bit :: rest) (pad :: pads) acc =>
      .deterministic { c with phase := .masking rest pads (Bool.xor bit pad :: acc) }
  | .masking _ _ acc => .deterministic { c with phase := .reverseCipher acc [] }
  | .reverseCipher (bit :: rest) acc =>
      .deterministic { c with phase := .reverseCipher rest (bit :: acc) }
  | .reverseCipher [] cipher =>
      .deterministic { c with phase := .prependCounter c.counter (false :: cipher) }
  | .prependCounter (bit :: rest) acc =>
      .deterministic { c with phase := .prependCounter rest (bit :: acc) }
  | .prependCounter [] reply => .deterministic { c with phase := .deliver true (true :: reply) }
  | .deliver success reply =>
      match c.source.control with
      | .awaiting machine request =>
          .deterministic { c with phase := .source, counter := if success then true :: c.counter else c.counter, source := { c.source with control := .loading machine reply {}, reverseTrace := (request, reply) :: c.source.reverseTrace } }
      | _ => .deterministic { c with phase := .source, source := { c.source with control := .finished false } }

noncomputable def step (code : Code) (oracle : Interactive.BitOracle Unit)
    (c : Configuration) : ProbComp Configuration :=
  match transition code c with
  | .deterministic next => PMF.pure next
  | .random zero one => sampleBit.map (fun bit => if bit then one else zero)
  | .oracleCall saved request mask =>
      (oracle () request).map fun response =>
        { saved with phase := .masking mask response.2 [], reverseTrace := (request, response.2) :: saved.reverseTrace }

noncomputable def eval (code : Code) (oracle : Interactive.BitOracle Unit)
    (start : Configuration) : Nat → ProbComp Configuration
  | 0 => PMF.pure start
  | fuel + 1 => (eval code oracle start fuel).bind (step code oracle)

def result (c : Configuration) : Option Bool :=
  match c.phase with
  | .source => c.source.result
  | _ => none

def complete (c : Configuration) : Prop :=
  c.phase = .source ∧ c.source.complete

def HaltsWithin (code : Code) (oracle : Interactive.BitOracle Unit)
    (start : Configuration) (fuel : Nat) : Prop :=
  ∀ finish ∈ (eval code oracle start fuel).support, complete finish

/-- A computable interpreter for deterministic fixtures and fixed local coins. -/
def simulateStep (code : Code) (oracle : List Bool → List Bool) (coin : Bool)
    (c : Configuration) : Configuration :=
  match transition code c with
  | .deterministic next => next
  | .random zero one => if coin then one else zero
  | .oracleCall saved request mask =>
      let response := oracle request
      { saved with phase := .masking mask response [], reverseTrace := (request, response) :: saved.reverseTrace }

def simulate (code : Code) (oracle : List Bool → List Bool) (coin : Bool) :
    Nat → Configuration → Configuration × Nat
  | 0, c => (c, 0)
  | fuel + 1, c =>
      if (result c).isSome then (c, 0)
      else
        let (finish, used) := simulate code oracle coin fuel (simulateStep code oracle coin c)
        (finish, used + 1)

theorem eval_add (code : Code) (oracle : Interactive.BitOracle Unit)
    (start : Configuration) (fuel extra : Nat) :
    eval code oracle start (fuel + extra) =
      (eval code oracle start fuel).bind (fun c => eval code oracle c extra) := by
  induction extra with
  | zero => simp [eval]
  | succ extra ih => rw [Nat.add_succ, eval, ih, PMF.bind_bind]; rfl

theorem eval_head (code : Code) (oracle : Interactive.BitOracle Unit)
    (start : Configuration) (fuel : Nat) :
    eval code oracle start (fuel + 1) =
      (step code oracle start).bind (fun c => eval code oracle c fuel) := by
  rw [show fuel + 1 = 1 + fuel by omega, eval_add]
  simp [eval]

def interleave : List Bool → List Bool → List Bool
  | left :: ls, right :: rs => left :: right :: interleave ls rs
  | _, _ => []

def xorList : List Bool → List Bool → List Bool
  | bit :: bits, pad :: pads => Bool.xor bit pad :: xorList bits pads
  | _, _ => []

/-- The selection cost includes both cells of each plaintext pair. -/
theorem select_eval (code : Code) (oracle : Interactive.BitOracle Unit) (c : Configuration)
    (left right acc : List Bool) (h : left.length = right.length) :
    eval code oracle { c with phase := .select (interleave left right) acc } (left.length + 1) =
      PMF.pure { c with phase := .reverseMask ((if code.side then right else left).reverse ++ acc) [] } := by
  induction left generalizing right acc with
  | nil =>
      have hr : right = [] := List.length_eq_zero_iff.mp h.symm
      subst right
      simp [eval, step, transition, interleave]
  | cons bit rest ih =>
      cases right with
      | nil => simp at h
      | cons r rs =>
          have ht : rest.length = rs.length := by simpa using h
          rw [List.length_cons, eval_head]
          simp only [step, transition, interleave, PMF.pure_bind]
          rw [ih rs _ ht]
          cases code.side <;> simp [List.reverse_cons, List.append_assoc]

/-- XOR processes one message and one pad cell per transition. -/
theorem masking_eval (code : Code) (oracle : Interactive.BitOracle Unit) (c : Configuration)
    (mask pad acc : List Bool) (h : mask.length = pad.length) :
    eval code oracle { c with phase := .masking mask pad acc } (mask.length + 1) =
      PMF.pure { c with phase := .reverseCipher ((xorList mask pad).reverse ++ acc) [] } := by
  induction mask generalizing pad acc with
  | nil =>
      have hp : pad = [] := List.length_eq_zero_iff.mp h.symm
      subst pad
      simp [eval, step, transition, xorList]
  | cons bit rest ih =>
      cases pad with
      | nil => simp at h
      | cons p ps =>
          have ht : rest.length = ps.length := by simpa using h
          rw [List.length_cons, eval_head]
          simp only [step, transition, PMF.pure_bind]
          rw [ih ps _ ht]
          simp [xorList, List.reverse_cons, List.append_assoc]


/-- Reversal and counter transfer are charged one cell at a time. -/
theorem reverseMask_eval (code : Code) (oracle : Interactive.BitOracle Unit) (c : Configuration)
    (bits acc : List Bool) :
    eval code oracle { c with phase := .reverseMask bits acc } (bits.length + 1) =
      PMF.pure { c with phase := .copyCounter c.counter [false] (bits.reverse ++ acc) } := by
  induction bits generalizing acc with
  | nil => simp [eval, step, transition]
  | cons bit rest ih =>
      rw [List.length_cons, eval_head]
      simp only [step, transition, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem copyCounter_eval (code : Code) (oracle : Interactive.BitOracle Unit) (c : Configuration)
    (bits acc mask : List Bool) :
    eval code oracle { c with phase := .copyCounter bits acc mask } (bits.length + 1) =
      PMF.pure { c with phase := .awaiting (bits.reverse ++ acc) mask } := by
  induction bits generalizing acc with
  | nil => simp [eval, step, transition]
  | cons bit rest ih =>
      rw [List.length_cons, eval_head]
      simp only [step, transition, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem reverseCipher_eval (code : Code) (oracle : Interactive.BitOracle Unit) (c : Configuration)
    (bits acc : List Bool) :
    eval code oracle { c with phase := .reverseCipher bits acc } (bits.length + 1) =
      PMF.pure { c with phase := .prependCounter c.counter (false :: (bits.reverse ++ acc)) } := by
  induction bits generalizing acc with
  | nil => simp [eval, step, transition]
  | cons bit rest ih =>
      rw [List.length_cons, eval_head]
      simp only [step, transition, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem prependCounter_eval (code : Code) (oracle : Interactive.BitOracle Unit) (c : Configuration)
    (bits acc : List Bool) :
    eval code oracle { c with phase := .prependCounter bits acc } (bits.length + 1) =
      PMF.pure { c with phase := .deliver true (true :: (bits.reverse ++ acc)) } := by
  induction bits generalizing acc with
  | nil => simp [eval, step, transition]
  | cons bit rest ih =>
      rw [List.length_cons, eval_head]
      simp only [step, transition, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]


theorem xorList_length (mask pad : List Bool) (h : mask.length = pad.length) :
    (xorList mask pad).length = mask.length := by
  induction mask generalizing pad with
  | nil => simp [xorList]
  | cons bit rest ih =>
      cases pad with
      | nil => simp at h
      | cons p ps => simp [xorList, ih ps (by simpa using h)]

theorem awaiting_eval (code : Code) (oracle : Interactive.BitOracle Unit) (c : Configuration)
    (request mask : List Bool) :
    eval code oracle { c with phase := .awaiting request mask } 1 =
      (oracle () request).map (fun response =>
        { c with phase := .masking mask response.2 [], reverseTrace := (request, response.2) :: c.reverseTrace }) := by
  simp [eval, step, transition]

/-- The exact per-call controller cost counts plaintext selection, every
counter transfer, the PRF capability, XOR, and ciphertext reconstruction.
Delivery to the source loader takes one further transition. -/
theorem query_controller_eval (code : Code) (oracle : Interactive.BitOracle Unit)
    (c : Configuration) (left right pad : List Bool) (h : left.length = right.length)
    (hp : pad.length = left.length)
    (response : oracle () (c.counter.reverse ++ [false]) = PMF.pure ((), pad)) :
    eval code oracle { c with phase := .select (interleave left right) [] }
      (4 * left.length + 2 * c.counter.length + 7) =
    PMF.pure { c with phase := .deliver true (true :: (c.counter.reverse ++ false :: xorList (if code.side then right else left) pad)), reverseTrace := (c.counter.reverse ++ [false], pad) :: c.reverseTrace } := by
  let mask := if code.side then right else left
  have hm : mask.length = left.length := by cases hs : code.side <;> simp [mask, hs, h]
  have hmp : mask.length = pad.length := hm.trans hp.symm
  have hx := xorList_length mask pad hmp
  have ht : 4 * left.length + 2 * c.counter.length + 7 =
      (left.length + 1) + ((mask.reverse.length + 1) + ((c.counter.length + 1) +
      (1 + ((mask.length + 1) + (((xorList mask pad).reverse.length + 1) +
      (c.counter.length + 1)))))) := by simp only [List.length_reverse]; omega
  rw [ht, eval_add, select_eval code oracle c left right [] h, PMF.pure_bind]
  simp only [List.append_nil]
  change eval code oracle { c with phase := .reverseMask mask.reverse [] } _ = _
  rw [eval_add, reverseMask_eval, PMF.pure_bind]
  simp only [List.reverse_reverse, List.append_nil]
  rw [eval_add, copyCounter_eval, PMF.pure_bind]
  rw [eval_add, awaiting_eval, response, PMF.pure_map, PMF.pure_bind]
  rw [eval_add, masking_eval code oracle { c with reverseTrace := (c.counter.reverse ++ [false], pad) :: c.reverseTrace } mask pad [] hmp, PMF.pure_bind]
  simp only [List.append_nil]
  rw [eval_add, reverseCipher_eval code oracle { c with reverseTrace := (c.counter.reverse ++ [false], pad) :: c.reverseTrace } (xorList mask pad).reverse [], PMF.pure_bind]
  simp only [List.reverse_reverse, List.append_nil]
  rw [prependCounter_eval code oracle { c with reverseTrace := (c.counter.reverse ++ [false], pad) :: c.reverseTrace } c.counter (false :: xorList mask pad)]


/-- Delivery resumes the existing cell-by-cell source response loader.
It records the ciphertext, then advances the unary counter on success only. -/
theorem deliver_eval (code : Code) (oracle : Interactive.BitOracle Unit) (c : Configuration)
    (machine : Machine.Configuration) (request reply : List Bool) (success : Bool)
    (h : c.source.control = .awaiting machine request) :
    eval code oracle { c with phase := .deliver success reply } 1 =
      PMF.pure { c with phase := .source, counter := if success then true :: c.counter else c.counter, source := { c.source with control := .loading machine reply {}, reverseTrace := (request, reply) :: c.source.reverseTrace } } := by
  simp [eval, step, transition, h]


/-- One successful source oracle transition is replaced by a finite,
resource-counted segment. The source resumes with the encoded ciphertext;
the target records precisely one PRF query at the old counter. -/
theorem query_success_eval (code : Code) (oracle : Interactive.BitOracle Unit)
    (c : Configuration) (machine : Machine.Configuration) (token : Bool) (rest : List Bool)
    (left right pad : List Bool) (h : left.length = right.length) (hp : pad.length = left.length)
    (phase : c.phase = .source) (capacity : c.capacity = token :: rest)
    (control : c.source.control = .awaiting machine (interleave left right))
    (response : oracle () (c.counter.reverse ++ [false]) = PMF.pure ((), pad)) :
    eval code oracle c (4 * left.length + 2 * c.counter.length + 9) =
    PMF.pure { c with capacity := rest, phase := .source, counter := true :: c.counter, source := { c.source with control := .loading machine (true :: (c.counter.reverse ++ false :: xorList (if code.side then right else left) pad)) {}, reverseTrace := (interleave left right, true :: (c.counter.reverse ++ false :: xorList (if code.side then right else left) pad)) :: c.source.reverseTrace }, reverseTrace := (c.counter.reverse ++ [false], pad) :: c.reverseTrace } := by
  let base : Configuration := { c with capacity := rest }
  have hs : step code oracle c =
      PMF.pure { base with phase := .select (interleave left right) [] } := by
    simp [step, transition, phase, Interactive.transition, control, capacity, base]
  have ht : 4 * left.length + 2 * c.counter.length + 9 =
      1 + ((4 * left.length + 2 * c.counter.length + 7) + 1) := by omega
  rw [ht, eval_add]
  have hone : eval code oracle c 1 = step code oracle c := by simp [eval]
  rw [hone, hs, PMF.pure_bind]
  change eval code oracle { base with phase := .select (interleave left right) [] }
    ((4 * left.length + 2 * base.counter.length + 7) + 1) = _
  rw [eval_add, query_controller_eval code oracle base left right pad h hp response, PMF.pure_bind]
  rw [deliver_eval code oracle { base with reverseTrace := (c.counter.reverse ++ [false], pad) :: c.reverseTrace }
    machine (interleave left right) _ true control]
  rfl


/-- Exhaustion is handled locally in two transitions. Neither the counter
nor the PRF transcript changes, and no oracle capability is invoked. -/
theorem query_exhausted_eval (code : Code) (oracle : Interactive.BitOracle Unit)
    (c : Configuration) (machine : Machine.Configuration) (request : List Bool)
    (phase : c.phase = .source) (capacity : c.capacity = [])
    (control : c.source.control = .awaiting machine request) :
    eval code oracle c 2 =
    PMF.pure { c with phase := .source, source := { c.source with control := .loading machine [false] {}, reverseTrace := (request, [false]) :: c.source.reverseTrace } } := by
  simp [eval, step, transition, phase, Interactive.transition, control, capacity]


/-- Completed executions absorb further fuel without changing either trace. -/
theorem step_complete (code : Code) (oracle : Interactive.BitOracle Unit)
    (c : Configuration) (h : complete c) : step code oracle c = PMF.pure c := by
  obtain ⟨phase, bit, control⟩ := h
  simp [step, transition, phase, Interactive.transition, control]
  cases c
  simp_all

theorem eval_stable (code : Code) (oracle : Interactive.BitOracle Unit)
    (start : Configuration) (fuel extra : Nat) (h : HaltsWithin code oracle start fuel) :
    eval code oracle start (fuel + extra) = eval code oracle start fuel := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ, eval, ih, ← PMF.bindOnSupport_eq_bind]
      calc
        (eval code oracle start fuel).bindOnSupport (fun c _ => step code oracle c) =
            (eval code oracle start fuel).bindOnSupport (fun c _ => PMF.pure c) := by
          congr 1
          funext c hc
          exact step_complete code oracle c (h c hc)
        _ = eval code oracle start fuel := PMF.bindOnSupport_pure _

theorem HaltsWithin.mono {code : Code} {oracle : Interactive.BitOracle Unit}
    {start : Configuration} {fuel fuel' : Nat} (h : HaltsWithin code oracle start fuel)
    (hle : fuel ≤ fuel') : HaltsWithin code oracle start fuel' := by
  have heq := eval_stable code oracle start fuel (fuel' - fuel) h
  rw [Nat.add_sub_of_le hle] at heq
  intro finish hf
  rw [heq] at hf
  exact h finish hf

end CryptoOracle.CounterMasking
