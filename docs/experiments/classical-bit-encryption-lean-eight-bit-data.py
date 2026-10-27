"""Generate candidate integer count data; Lean certificates establish validity.

The generator reuses the archived exact rounding algorithm without changing it.
It performs no network access. Generated declarations are computable integers.
"""
from pathlib import Path
import importlib.util

ROOT = Path(__file__).resolve().parents[2]
ROUNDING = ROOT / 'docs/experiments/classical-bit-encryption-mesh-separation.py'
OUTPUT = ROOT / 'Foundation/Crypto/Semantics/Probability/ClassicalBitEightBitData.lean'


def main():
    spec = importlib.util.spec_from_file_location('archived_mesh_rounding', ROUNDING)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    lines = ['import Mathlib', '', '/-! Generated candidate data for the N=32, eight-bit table.',
             'Validity is established in separate kernel-checked certificate modules. -/',
             'namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable',
             'open scoped BigOperators', '']
    for a in range(33):
        for b in range(a, 33):
            entries = []
            for c in range(b, 33):
                x = (a, b-a, c-b, 32-c)
                minimum = min(x)
                raw = [32-4*v+3*minimum for v in x] + [-12*minimum]
                entries.extend(module.balanced_counts(raw))
            lines.append(f'def row_{a}_{b} : Array ℤ := #[' + ','.join(map(str, entries)) + ']')
        lines += ['', f'def rows_{a} (b c k : ℕ) : ℤ :=', '  match b with']
        for b in range(a, 33):
            lines.append(f'  | {b} => row_{a}_{b}.getD ((c-{b})*5+k) 0')
        lines += ['  | _ => 0', '']
    lines += ['def counts (a b c k : ℕ) : ℤ :=', '  match a with']
    lines += [f'  | {a} => rows_{a} b c k' for a in range(33)]
    lines += ['  | _ => 0', '', 'def boundary (a b c : ℕ) : Prop :=',
              '  a = 0 ∨ a = b ∨ b = c ∨ c = 32', '',
              'def rawFour (a b c : ℕ) (k : Fin 4) : ℤ :=',
              '  if k.val = 0 then 32-4*(a : ℤ) else',
              '  if k.val = 1 then 32-4*((b : ℤ)-(a : ℤ)) else',
              '  if k.val = 2 then 32-4*((c : ℤ)-(b : ℤ)) else 32-4*(32-(c : ℤ))', '',
              'def vertexCheck (a b c : ℕ) : Prop :=',
              '  (∑ k : Fin 5, counts a b c k.val) = 0 ∧',
              '  (∑ k : Fin 5, |counts a b c k.val|) = 256 ∧',
              '  (boundary a b c → counts a b c 4 = 0 ∧',
              '    0 < (∑ k : Fin 4, |rawFour a b c k|) ∧',
              '    ∀ k : Fin 4, |counts a b c k.val*(∑ j : Fin 4, |rawFour a b c j|)-',
              '      rawFour a b c k*256| ≤ ∑ j : Fin 4, |rawFour a b c j|)', '',
              'def vertexRowCheck (a : ℕ) : Prop :=',
              '  ∀ b c : Fin 33, a ≤ b.val → b.val ≤ c.val → vertexCheck a b.val c.val', '',
              'end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable', '']
    OUTPUT.write_text('\n'.join(lines))
    print(f'Wrote {OUTPUT.relative_to(ROOT)} ({OUTPUT.stat().st_size} bytes).')


if __name__ == '__main__':
    main()
