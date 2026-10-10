import Foundation.Constructions.Hash.NativeTypedCompression
import Foundation.Crypto.Semantics.Machine.DelimitedTapeEquality

/-! Physical entry-key comparison for the fixed compression simulator.
The existing compression-packet encoding is retained. A delimited tape
layout supports subsequent sequential lookup; it is not a host lookup.
The table loop, delimiter restoration and value copying remain separate. -/
namespace Foundation.Hash.Native.SimulatorLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false

/-- A record marker, one self-delimited compression input and its raw
fixed-width digest. All records retain the original list order. -/
def entryBits {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n) : List Bool :=
  true :: FiniteBitEncoding.delimit (compressionPacket entry.1) ++ entry.2.toList

/-- An explicit false record marker terminates the finite table. This is
a physical layout description, not a constant-time encoder instruction. -/
def tableBits {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n)) : List Bool :=
  table.flatMap entryBits ++ [false]

@[simp] theorem tableBits_nil {n κ : Nat} : tableBits (n := n) (κ := κ) [] = [false] := rfl

theorem tableBits_cons {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (rest : CompressionTable (Bits κ) (Bits n)) :
    tableBits (entry :: rest) = entryBits entry ++ tableBits rest := by
  simp [tableBits, List.append_assoc]

theorem entryBits_length {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n) :
    (entryBits entry).length = 3 * n + 2 * κ + 4 := by
  simp only [entryBits, List.length_cons, List.length_append, FiniteBitEncoding.delimit_length,
    compressionPacket_length, Bits.length_toList]
  omega

theorem tableBits_length {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n)) :
    (tableBits table).length = (3 * n + 2 * κ + 4) * table.length + 1 := by
  induction table with
  | nil => simp
  | cons entry rest ih =>
      rw [tableBits_cons, List.length_append, entryBits_length, ih, List.length_cons]
      ring

theorem compression_packet_eq_iff {n κ : Nat}
    (first second : CompressionInput (Bits κ) (Bits n)) :
    compressionPacket first = compressionPacket second ↔ first = second := by
  constructor
  · intro same
    apply compressionKey_injective n κ
    simp only [compressionKey, same]
  · intro same
    rw [same]

def comparisonInput {n κ : Nat}
    (candidate query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (tail suffix : List Bool) : DelimitedTapeEquality.Input where
  beforeInput := beforeInput
  beforeOutput := beforeOutput
  candidate := compressionPacket candidate
  query := compressionPacket query
  tail := tail
  suffix := suffix
  width := by rw [compressionPacket_length, compressionPacket_length]

theorem comparison_run {n κ : Nat}
    (candidate query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (tail suffix : List Bool) :
    evalConfigWithin DelimitedTapeEquality.program
      (DelimitedTapeEquality.start (comparisonInput candidate query beforeInput beforeOutput tail suffix))
      (7 * (n + κ + 1) + 3) =
    PMF.pure (DelimitedTapeEquality.finish
      (comparisonInput candidate query beforeInput beforeOutput tail suffix)) := by
  simpa only [comparisonInput, compressionPacket_length] using
    DelimitedTapeEquality.run (comparisonInput candidate query beforeInput beforeOutput tail suffix)

/-- The computed bit tests the original typed compression input, including
its digest, data/terminal marker and payload. It is not merely a digest test. -/
theorem comparison_status {n κ : Nat}
    (candidate query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (tail suffix : List Bool) :
    (DelimitedTapeEquality.finish
      (comparisonInput candidate query beforeInput beforeOutput tail suffix)).inputTape.current =
      some (decide (candidate = query)) := by
  rw [DelimitedTapeEquality.status]
  simp only [comparisonInput, compression_packet_eq_iff]

theorem comparison_first_joint {n κ : Nat}
    (candidate query : CompressionInput (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (tail suffix : List Bool) :
    runToBoundary (stepPMF DelimitedTapeEquality.program) Configuration.halted
      (7 * (n + κ + 1) + 3)
      (DelimitedTapeEquality.start (comparisonInput candidate query beforeInput beforeOutput tail suffix)) =
    PMF.pure (DelimitedTapeEquality.finish
      (comparisonInput candidate query beforeInput beforeOutput tail suffix), 7 * (n + κ + 1) + 3) := by
  simpa only [comparisonInput, compressionPacket_length] using
    DelimitedTapeEquality.first_joint (comparisonInput candidate query beforeInput beforeOutput tail suffix)

end Foundation.Hash.Native.SimulatorLookup
