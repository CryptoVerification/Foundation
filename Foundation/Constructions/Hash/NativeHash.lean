import Foundation.Constructions.Hash.NativeIteration

/-! End-to-end native execution of a finite, specialized hash computation.
The initialization writes every initial-digest bit and rewinds its real tape.
The emitted code is independent of all oracle responses. Specialization of the
message is explicit; this is not a uniform parser for runtime message inputs. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open StraightLine
set_option backward.isDefEq.respectTransparency false

def initializeActions (initial : List Bool) : List Action :=
  writeActions initial ++ leftActions initial.length

@[simp] theorem initializeActions_length (initial : List Bool) :
    (initializeActions initial).length = 3 * initial.length := by
  simp [initializeActions]
  omega

theorem initialize_execute (pc : Nat) (input : Tape) (initial : List Bool) :
    execute (initializeActions initial) { pc := pc, inputTape := input } =
      ({ pc := pc + 3 * initial.length, inputTape := input, outputTape := ResponseLoading.loaded initial } : Machine.Configuration) := by
  rw [initializeActions, execute_append]
  have h := write_execute pc input [] initial
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at h
  rw [h]
  rw [show initial.length = initial.reverse.length by simp, left_execute]
  simp only [List.reverse_reverse, List.length_reverse, ResponseLoading.loaded]
  congr 1; omega

def initializedCode (initial : List Bool) (blocks : List (List Bool)) : Code :=
  StraightLine.code (initializeActions initial) ++ iterationCode initial.length blocks

/-- Genuine native termination and full joint realization from an initially
blank output tape. The input tape is preserved, not consulted by this specialized
code. Runtime includes initialization and the final native halt. -/
theorem initialized_run {State : Type*} (oracle : BitOracle State)
    (initial : List Bool) (blocks : List (List Bool)) (input : List Bool) (state : State)
    (width : ∀ state request answer, answer ∈ (oracle state request).support →
      answer.2.length = initial.length) :
    Reification.eval (initializedCode initial blocks) oracle
      (3 * initial.length + iterationSteps initial.length blocks)
      (Configuration.initial state input) =
    ((Foundation.Hash.iterate initial blocks).run
      (Program.adaptOracle (fun pair => pair.1 ++ pair.2) id oracle) state).map
      (iterationFinish ((initializedCode initial blocks).length - 1) (Tape.ofBits input) []) := by
  rw [← Reification.timed_eval_eq, TimedExecution.eval_add]
  have init := StraightLine.public_run oracle state [] [] (iterationCode initial.length blocks)
    (initializeActions initial) (Machine.Configuration.initial input) rfl rfl
  rw [initializeActions_length] at init
  change TimedExecution.eval _ _
    (⟨state, .running { pc := 0, inputTape := Tape.ofBits input }, []⟩ : Configuration State) = _ at init
  simp only [Machine.Configuration.initial] at init
  rw [initialize_execute] at init
  simp only [List.nil_append, Nat.zero_add] at init
  change (TimedExecution.eval (Reification.timedStep (initializedCode initial blocks) oracle)
    (3 * initial.length) _).bind _ = _
  simp only [initializedCode, Interactive.Configuration.initial, Machine.Configuration.initial]
  rw [init, PMF.pure_bind]
  have h := iteration_run oracle initial.length width
    (StraightLine.code (initializeActions initial)) [] (Tape.ofBits input) state [] initial blocks rfl
  simpa only [initializedCode, List.append_nil, List.length_append, StraightLine.code,
    List.length_map, initializeActions_length] using h

/-- Every supported execution actually halts. Fuel exhaustion does not count
as success; the final native tape still contains the entire resulting digest. -/
theorem initialized_halts {State : Type*} (oracle : BitOracle State)
    (initial : List Bool) (blocks : List (List Bool)) (input : List Bool) (state : State)
    (width : ∀ state request answer, answer ∈ (oracle state request).support →
      answer.2.length = initial.length) :
    Reification.HaltsWithin (initializedCode initial blocks) oracle
      (Configuration.initial state input)
      (3 * initial.length + iterationSteps initial.length blocks) := by
  intro finish hFinish
  rw [initialized_run oracle initial blocks input state width, PMF.mem_support_map_iff] at hFinish
  obtain ⟨out, _, rfl⟩ := hFinish
  rfl

/-- Total native duration when every marked block has the same public width. -/
theorem iterationSteps_fixed_width (digestWidth blockWidth : Nat) (blocks : List (List Bool))
    (width : ∀ block ∈ blocks, block.length = blockWidth) :
    iterationSteps digestWidth blocks = blocks.length * (7 * digestWidth + 5 * blockWidth + 6) + 1 := by
  induction blocks with
  | nil => simp [iterationSteps]
  | cons block rest ih =>
      rw [iterationSteps, width block (by simp), ih (fun b hb => width b (by simp [hb]))]
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Changing block representation reuses the existing query adapter and
retains the whole joint state/result/transcript distribution. -/
theorem iterate_encoded_run {Payload Encoded Digest : Type} {State : Type*}
    (encoding : Payload → Encoded) (initial : Digest) (blocks : List Payload)
    (oracle : Oracle (Digest × Encoded) Digest State) (state : State) :
    ((Foundation.Hash.iterate initial (blocks.map encoding)).run oracle state) =
      ((Foundation.Hash.iterate initial blocks).run
        (Program.adaptOracle (fun pair : Digest × Payload => (pair.1, encoding pair.2)) id oracle) state).map
        (Program.mapTranscript (fun pair : Digest × Payload => (pair.1, encoding pair.2)) id) := by
  induction blocks generalizing initial state with
  | nil => simp [Foundation.Hash.iterate, Program.run, Program.mapTranscript, PMF.pure_map]
  | cons block rest ih =>
      simp only [List.map_cons, Foundation.Hash.iterate, Program.run,
        Program.adaptOracle, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      congr 1
      funext answer
      rw [ih]
      simp only [PMF.map_comp, Function.comp_def]
      congr 1

def markedBlocks (terminal : List Bool) (message : List (List Bool)) : List (List Bool) :=
  (Foundation.Hash.encode terminal message).map (fun block => block.1 :: block.2)

def prefixFreeCode (initial terminal : List Bool) (message : List (List Bool)) : Code :=
  initializedCode initial (markedBlocks terminal message)

def hashFinish {State : Type*} (pc : Nat) (input : Tape)
    (out : Outcome (List Bool × (Bool × List Bool)) (List Bool) (List Bool) State) :
    Configuration State :=
  ⟨out.state, .running { pc := pc, inputTape := input, outputTape := ResponseLoading.loaded out.result, halted := true },
    (out.trace.map (fun entry => (entry.1.1 ++ entry.1.2.1 :: entry.1.2.2, entry.2))).reverse⟩

/-- The actual native code realizes the original prefix-free MD definition
with raw bitstring compression packets. Fixed response width is the oracle
interface contract. This theorem does not idealize native packet preparation. -/
theorem prefixFree_run {State : Type*} (oracle : BitOracle State)
    (initial terminal : List Bool) (message : List (List Bool)) (input : List Bool) (state : State)
    (width : ∀ state request answer, answer ∈ (oracle state request).support →
      answer.2.length = initial.length) :
    Reification.eval (prefixFreeCode initial terminal message) oracle
      (3 * initial.length + iterationSteps initial.length (markedBlocks terminal message))
      (Configuration.initial state input) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run
      (Program.adaptOracle (fun pair => pair.1 ++ pair.2.1 :: pair.2.2) id oracle) state).map
      (hashFinish ((prefixFreeCode initial terminal message).length - 1) (Tape.ofBits input)) := by
  rw [prefixFreeCode, initialized_run oracle initial (markedBlocks terminal message) input state width,
    markedBlocks, iterate_encoded_run]
  have adapters :
      Program.adaptOracle (fun pair : List Bool × (Bool × List Bool) => (pair.1, pair.2.1 :: pair.2.2)) id
        (Program.adaptOracle (fun pair : List Bool × List Bool => pair.1 ++ pair.2) id oracle) =
      Program.adaptOracle (fun pair => pair.1 ++ pair.2.1 :: pair.2.2) id oracle := by
    funext s request
    simp [Program.adaptOracle, PMF.map_comp, Function.comp_def]
  rw [adapters]
  simp only [PMF.map_comp, Function.comp_def, Foundation.Hash.prefixFreeMD]
  congr 1
  funext out
  simp [hashFinish, iterationFinish, Program.mapTranscript, encodeIterationTrace,
    List.map_map, Function.comp_def]

/-- Explicit native transition budget for κ-bit payload blocks (including the terminal).
There is no fixed-width message-length field and no maximum block count. -/
theorem prefixFree_steps (initial terminal : List Bool) (message : List (List Bool))
    (payloadWidth : Nat) (terminalWidth : terminal.length = payloadWidth)
    (messageWidth : ∀ block ∈ message, block.length = payloadWidth) :
    3 * initial.length + iterationSteps initial.length (markedBlocks terminal message) =
      3 * initial.length + (message.length + 1) *
        (7 * initial.length + 5 * payloadWidth + 11) + 1 := by
  have h : ∀ block ∈ markedBlocks terminal message, block.length = payloadWidth + 1 := by
    intro block hb
    simp only [markedBlocks, Foundation.Hash.encode, List.map_append, List.map_map,
      List.map_singleton, List.mem_append, List.mem_map, List.mem_singleton] at hb
    rcases hb with ⟨original, hm, rfl⟩ | rfl
    · simp [messageWidth original hm]
    · simp [terminalWidth]
  rw [iterationSteps_fixed_width initial.length (payloadWidth + 1) _ h]
  simp [markedBlocks, Nat.mul_add, Nat.add_assoc]

end Foundation.Hash.Native
