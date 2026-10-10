import Foundation.Constructions.Hash.NativeSimulatorRewind

/-! Exact split of the physically traversed and unread table cells after
sequential lookup. This is a proof-side description, not an executed search
or a tape reset. It applies both to hits and misses, including duplicate keys. -/
namespace Foundation.Hash.Native.SimulatorLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

/-- Include the first matching record in the consumed prefix. -/
def lookupSplit {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n)) :
    CompressionTable (Bits κ) (Bits n) → List Bool × List Bool
  | [] => ([], [false])
  | entry :: rest =>
      if entry.1 = query then (entryBits entry, tableBits rest)
      else (entryBits entry ++ (lookupSplit query rest).1, (lookupSplit query rest).2)

theorem lookupSplit_table {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    (lookupSplit query table).1 ++ (lookupSplit query table).2 = tableBits table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      simp only [lookupSplit, tableBits_cons]
      split_ifs <;> simp only [List.append_assoc, ih]

theorem lookupSplit_unread_nonempty {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    (lookupSplit query table).2 ≠ [] := by
  induction table with
  | nil => simp [lookupSplit]
  | cons entry rest ih =>
      simp only [lookupSplit]
      split_ifs
      · have size := tableBits_length rest
        intro empty
        change tableBits rest = [] at empty
        rw [empty] at size
        simp at size
      · exact ih

/-- The scan traverses at most all records; the final sentinel remains unread. -/
theorem lookupSplit_prefix_length {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    (lookupSplit query table).1.length ≤ table.length * (3 * n + 2 * κ + 4) := by
  have layout := congrArg List.length (lookupSplit_table query table)
  rw [List.length_append, tableBits_length, Nat.mul_comm (3 * n + 2 * κ + 4)] at layout
  have nonempty := lookupSplit_unread_nonempty query table
  have positive : 0 < (lookupSplit query table).2.length := List.length_pos_iff.mpr nonempty
  omega

/-- Lookup's input head is just past the consumed records. The original
current cell and every unread cell survive, with no normalized tape quotient. -/
theorem lookupFinish_input {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    (lookupFinish query table beforeInput beforeOutput).inputTape =
      { Tape.ofBits (lookupSplit query table).2 with
        left := (lookupSplit query table).1.reverse.map some ++ beforeInput } := by
  induction table generalizing beforeInput with
  | nil => simp [lookupFinish, lookupSplit, missingFinish, scanStart, tableBits, Tape.ofBits]
  | cons entry rest ih =>
      simp only [lookupFinish, lookupSplit]
      split_ifs
      · cases unread : tableBits rest <;> simp [unread, foundFinish, entryBits, DelimitedTapeComparison.delimit_eq_marked,
          FixedWidthCopy.frontier,
          ResponseLoading.fromCells, List.reverse_append, List.map_append, List.append_assoc,
          Tape.ofBits]
      · rw [ih]
        simp [List.reverse_append, List.map_append, List.append_assoc]

/-- A contiguous bit prefix is restored exactly, retaining the outer blank
created by the actual left scan. This strengthens the old equivalence-only
suffix contract for the concrete native component used here. -/
theorem rewind_suffix_layout (prefixBits unread : List Bool) (other : Tape) (nonempty : unread ≠ []) :
    (NativeBitstringRewind.finish
      { bits := prefixBits, current := (Tape.ofBits unread).current,
        right := (Tape.ofBits unread).right, other := other }).inputTape =
      { Tape.ofBits (prefixBits ++ unread) with left := [none] } := by
  cases unread with
  | nil => exact False.elim (nonempty rfl)
  | cons bit rest =>
      cases prefixBits <;> simp [NativeBitstringRewind.finish, Tape.ofBits, Tape.moveRight, List.map_append]

def lookupRewindInput {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) : NativeBitstringRewind.Input where
  bits := (lookupSplit query table).1
  current := (Tape.ofBits (lookupSplit query table).2).current
  right := (Tape.ofBits (lookupSplit query table).2).right
  other := (lookupFinish query table [] beforeOutput).outputTape

theorem lookupRewind_entry {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    (lookupFinish query table [] beforeOutput).resumeAt 0 =
      NativeBitstringRewind.initial (lookupRewindInput query table beforeOutput) := by
  have layout := lookupFinish_input query table [] beforeOutput
  simp only [Configuration.resumeAt, NativeBitstringRewind.initial, lookupRewindInput,
    layout, List.append_nil]

theorem lookupRewind_table {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    (NativeBitstringRewind.finish (lookupRewindInput query table beforeOutput)).inputTape =
      { Tape.ofBits (tableBits table) with left := [none] } := by
  have h := rewind_suffix_layout (lookupSplit query table).1 (lookupSplit query table).2
    (lookupFinish query table [] beforeOutput).outputTape (lookupSplit_unread_nonempty query table)
  simpa only [lookupRewindInput, lookupSplit_table] using h

end Foundation.Hash.Native.SimulatorLookup
