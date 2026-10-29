"""Generate serially chained row modules with separate kernel checks per second coordinate.

The generated proofs, rather than this generator, certify the finite assertions.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'Foundation/Crypto/Semantics/Probability'
PREFIX = 'Foundation.Crypto.Semantics.Probability.'
NAMESPACE = 'Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable'
PREDICATES = """import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitData

/-! Shared predicates for the kernel-checked sliced neighbor certificates. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable
open scoped BigOperators

def neighborIncrement (mask : Fin 8) (j : Fin 3) : ℕ :=
  if j.val = 0 then mask.val % 2 else if j.val = 1 then (mask.val / 2) % 2 else (mask.val / 4) % 2

def neighborCheck (a b c : ℕ) (mask : Fin 8) : Prop :=
  let aa := a+neighborIncrement mask 0
  let bb := b+neighborIncrement mask 1
  let cc := c+neighborIncrement mask 2
  aa ≤ bb → bb ≤ cc → cc ≤ 32 →
    (∑ k : Fin 5, |counts a b c k.val-counts aa bb cc k.val|) ≤ 148

def neighborRowCheck (a : ℕ) : Prop :=
  ∀ b c : Fin 33, a ≤ b.val → b.val ≤ c.val → ∀ mask : Fin 8, neighborCheck a b.val c.val mask

instance neighborCheckDecidable (a b c : ℕ) (mask : Fin 8) : Decidable (neighborCheck a b c mask) := by
  unfold neighborCheck; infer_instance
instance neighborRowCheckDecidable (a : ℕ) : Decidable (neighborRowCheck a) := by
  unfold neighborRowCheck; infer_instance

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable
"""


def main():
    (BASE / 'ClassicalBitEightBitNeighborPredicates.lean').write_text(PREDICATES)
    directory = BASE / 'ClassicalBitEightBitNeighborRows'
    directory.mkdir(exist_ok=True)
    for a in range(33):
        previous = 'ClassicalBitEightBitNeighborPredicates' if a == 0 else f'ClassicalBitEightBitNeighborRows.Row{a-1}'
        text = f'import {PREFIX}{previous}\n\n'
        text += f'namespace {NAMESPACE}\n'
        text += 'set_option maxRecDepth 65536\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n'
        text += f'theorem neighborRow_{a}_checked : neighborRowCheck {a} := by\n'
        text += '  unfold neighborRowCheck\n  intro b\n  fin_cases b <;> decide +kernel\n\n'
        text += f'end {NAMESPACE}\n'
        (directory / f'Row{a}.lean').write_text(text)
    text = f'import {PREFIX}ClassicalBitEightBitNeighborRows.Row32\n\n'
    text += '/-! All binary neighbor certificates; the import chain keeps row builds serial. -/\n'
    text += f'namespace {NAMESPACE}\n\n'
    text += 'theorem neighbors_checked (a b c : Fin 33) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val)\n'
    text += '    (mask : Fin 8) : neighborCheck a.val b.val c.val mask := by\n  fin_cases a\n'
    text += ''.join(f'  · exact neighborRow_{a}_checked b c hab hbc mask\n' for a in range(33))
    text += f'\nend {NAMESPACE}\n'
    (BASE / 'ClassicalBitEightBitSlicedNeighborChecks.lean').write_text(text)


if __name__ == '__main__':
    main()
