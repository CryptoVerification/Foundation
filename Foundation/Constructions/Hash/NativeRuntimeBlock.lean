import Foundation.Constructions.Hash.NativePreparation
import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy

/-! A compression fragment whose payload is read from the input tape.
Its code depends only on widths and addresses. Contiguous payloads need no
blank separator; the exact unconsumed input and preceding cells are retained.
Only the oracle capability itself is atomic; all tape work is native code. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open StraightLine
set_option backward.isDefEq.respectTransparency false

/-- Append the data marker and consume it from the input. -/
def runtimePrefix (digestWidth : Nat) : List Action :=
  rightActions digestWidth ++
    [.write .output (some false), .right .output, .right .input]

@[simp] theorem runtimePrefix_length (n : Nat) : (runtimePrefix n).length = n + 3 := by
  simp [runtimePrefix]

theorem runtimePrefix_execute (pc : Nat) (input : Tape) (digest : List Bool) :
    execute (runtimePrefix digest.length)
      { pc := pc, inputTape := input, outputTape := ResponseLoading.loaded digest } =
    ({ pc := pc + digest.length + 3, inputTape := input.moveRight, outputTape := { left := some false :: digest.reverse.map some } } : Machine.Configuration) := by
  rw [runtimePrefix, execute_append]
  have h := right_execute pc input digest []
  rw [show ({ ResponseLoading.loaded digest with left := [] } : Tape) = ResponseLoading.loaded digest from rfl] at h
  rw [h]
  simp [execute, apply, Machine.Configuration.updateTape, Machine.Configuration.advance,
    Tape.write, Tape.moveRight, Nat.add_assoc]

/-- Read exactly κ payload bits after their data marker, then rewind. -/
def runtimePrepareCode (base n κ fault : Nat) : Code :=
  StraightLine.code (runtimePrefix n) ++
  FixedWidthCopy.code (base + n + 3) κ fault ++
  StraightLine.code (leftActions (n + κ + 1))

@[simp] theorem runtimePrepareCode_length (base n κ fault : Nat) :
    (runtimePrepareCode base n κ fault).length = 2 * n + 8 * κ + 4 := by
  simp [runtimePrepareCode, StraightLine.code]
  omega

/-- The data marker is part of the caller's valid input condition. -/
theorem runtime_prepare_run {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (before after : Code)
    (fault : Nat) (beforeInput tail : List (Option Bool)) (digest payload : List Bool) :
    TimedExecution.eval
      (Reification.timedStep (before ++ runtimePrepareCode before.length digest.length payload.length fault ++ after) oracle)
      (2 * digest.length + 6 * payload.length + 4)
      (⟨state, .running { pc := before.length, inputTape := FixedWidthCopy.frontier beforeInput (some false :: (payload.map some ++ tail)), outputTape := ResponseLoading.loaded digest }, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running { pc := before.length + (2 * digest.length + 8 * payload.length + 4), inputTape := FixedWidthCopy.frontier ((false :: payload).reverse.map some ++ beforeInput) tail, outputTape := ResponseLoading.loaded (digest ++ false :: payload) }, trace⟩ := by
  rw [show 2 * digest.length + 6 * payload.length + 4 =
      (digest.length + 3) + (5 * payload.length + (digest.length + payload.length + 1)) by omega,
    TimedExecution.eval_add]
  have prefixRun := StraightLine.public_run oracle state trace before
    (FixedWidthCopy.code (before.length + digest.length + 3) payload.length fault ++
      StraightLine.code (leftActions (digest.length + payload.length + 1)) ++ after)
    (runtimePrefix digest.length)
    { pc := before.length, inputTape := FixedWidthCopy.frontier beforeInput (some false :: (payload.map some ++ tail)), outputTape := ResponseLoading.loaded digest } rfl rfl
  rw [runtimePrefix_length, runtimePrefix_execute] at prefixRun
  simp only [runtimePrepareCode, List.append_assoc] at prefixRun ⊢
  rw [prefixRun, PMF.pure_bind, FixedWidthCopy.frontier_move, TimedExecution.eval_add]
  have copy := FixedWidthCopy.run oracle state trace
    (before ++ StraightLine.code (runtimePrefix digest.length))
    (StraightLine.code (leftActions (digest.length + payload.length + 1)) ++ after)
    fault (some false :: beforeInput) (some false :: digest.reverse.map some) tail payload
  simp only [List.length_append, StraightLine.code, List.length_map, runtimePrefix_length,
    List.append_assoc, Nat.add_assoc] at copy
  simp only [Nat.add_assoc, StraightLine.code] at ⊢
  rw [copy, PMF.pure_bind]
  have rewind := StraightLine.public_run oracle state trace
    (before ++ StraightLine.code (runtimePrefix digest.length) ++
      FixedWidthCopy.code (before.length + digest.length + 3) payload.length fault)
    after (leftActions (digest.length + payload.length + 1))
    { pc := before.length + digest.length + 3 + 7 * payload.length, inputTape := FixedWidthCopy.frontier (payload.reverse.map some ++ some false :: beforeInput) tail, outputTape := { left := payload.reverse.map some ++ some false :: digest.reverse.map some } }
    (by simp [StraightLine.code]; omega) rfl
  have left := left_execute
    (before.length + digest.length + 3 + 7 * payload.length)
    (FixedWidthCopy.frontier (payload.reverse.map some ++ some false :: beforeInput) tail)
    (digest ++ false :: payload).reverse none []
  simp only [List.length_reverse, List.length_append, List.length_cons] at left
  simp only [List.reverse_append, List.reverse_cons, List.map_append, List.map_cons,
    List.singleton_append, List.append_assoc] at left
  simp only [Nat.add_assoc] at left rewind
  rw [leftActions_length, left] at rewind
  have pc_eq : before.length + digest.length + 3 + 7 * payload.length +
      (digest.length + payload.length + 1) = before.length + (2 * digest.length + 8 * payload.length + 4) := by omega
  simp only [Nat.add_assoc] at pc_eq
  rw [pc_eq] at rewind
  simpa [StraightLine.code, ResponseLoading.loaded, List.append_assoc, List.reverse_cons, List.map_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using rewind

/-- The same code serves all payload values of a given width. -/
def runtimeDataCode (base n κ fault : Nat) : Code :=
  runtimePrepareCode base n κ fault ++ [.call]

@[simp] theorem runtimeDataCode_length (base n κ fault : Nat) :
    (runtimeDataCode base n κ fault).length = 2 * n + 8 * κ + 5 := by
  simp [runtimeDataCode]

/-- Full call law, with the exact private state, transcript and input suffix.
The duration excludes the internal computation of the oracle capability. -/
theorem runtime_data_run {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (before after : Code)
    (fault : Nat) (beforeInput tail : List (Option Bool)) (digest payload : List Bool)
    (width : ∀ answer ∈ (oracle state (digest ++ false :: payload)).support,
      answer.2.length = digest.length) :
    TimedExecution.eval
      (Reification.timedStep (before ++ runtimeDataCode before.length digest.length payload.length fault ++ after) oracle)
      (7 * digest.length + 8 * payload.length + 12)
      (⟨state, .running { pc := before.length, inputTape := FixedWidthCopy.frontier beforeInput (some false :: (payload.map some ++ tail)), outputTape := ResponseLoading.loaded digest }, trace⟩ : Configuration State) =
    (oracle state (digest ++ false :: payload)).map (fun answer =>
      (⟨answer.1, .running { pc := before.length + (2 * digest.length + 8 * payload.length + 4) + 1, inputTape := FixedWidthCopy.frontier ((false :: payload).reverse.map some ++ beforeInput) tail, outputTape := ResponseLoading.loaded answer.2 },
        (digest ++ false :: payload, answer.2) :: trace⟩ : Configuration State)) := by
  rw [show 7 * digest.length + 8 * payload.length + 12 =
      (2 * digest.length + 6 * payload.length + 4) +
        (2 * (digest ++ false :: payload).length + 3 * digest.length + 6) by simp; omega,
    TimedExecution.eval_add]
  have prep := runtime_prepare_run oracle state trace before (.call :: after) fault beforeInput tail digest payload
  simp only [runtimeDataCode, List.append_assoc, List.singleton_append] at prep ⊢
  rw [prep, PMF.pure_bind]
  exact CallExecution.run _ oracle _ state trace (digest ++ false :: payload) digest.length rfl
    (by
      have pos : before.length + (2 * digest.length + 8 * payload.length + 4) =
          (before ++ runtimePrepareCode before.length digest.length payload.length fault).length := by simp
      rw [pos]
      simp [← List.append_assoc]) rfl width

end Foundation.Hash.Native
