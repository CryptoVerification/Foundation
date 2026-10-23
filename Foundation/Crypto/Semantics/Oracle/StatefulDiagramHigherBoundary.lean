import Foundation.Crypto.Semantics.Oracle.StatefulDiagramHigher

/-! Audit the scope of the three higher exchange schemata, rather than
assuming they already give a coherent presentation for repeated identifiers. -/
namespace CryptoOracle.StatefulDiagram
variable {Slot Op : Type} [DecidableEq Slot]

private theorem count_heq (signature : Op → Interface Slot) {a b c d : List Op}
    (source : a = c) (target : b = d)
    {one : Exchange signature a b} {two : Exchange signature c d} (same : HEq one two) :
    one.swapCount signature = two.swapCount signature := by
  cases source
  cases target
  exact congrArg (Exchange.swapCount signature) (eq_of_heq same)

theorem Exchange.swapCount_whisker (signature : Op → Interface Slot) {one two : List Op}
    (certificate : Exchange signature one two) (past future : List Op) :
    (certificate.whisker signature past future).swapCount signature = certificate.swapCount signature := by
  induction certificate with
  | refl => rfl
  | swap before after first second accepted =>
      have source : past ++ (before ++ [first, second] ++ after) ++ future =
          (past ++ before) ++ [first, second] ++ (after ++ future) := by simp only [List.append_assoc]
      have target : past ++ (before ++ [second, first] ++ after) ++ future =
          (past ++ before) ++ [second, first] ++ (after ++ future) := by simp only [List.append_assoc]
      have equalCount := count_heq signature source target
        (one := (Exchange.swap before after first second accepted).whisker signature past future)
        (two := Exchange.swap (past ++ before) (after ++ future) first second accepted) (by
          simp only [Exchange.whisker]
          exact (cast_heq _ _).trans (cast_heq _ _))
      simpa only [Exchange.swapCount] using equalCount
  | symm certificate ih => exact ih
  | trans first second ihFirst ihSecond =>
      change (first.whisker signature past future).swapCount signature +
        (second.whisker signature past future).swapCount signature = _
      rw [ihFirst, ihSecond]
      rfl

private theorem add_parity {a b c d : Nat} (first : a % 2 = b % 2) (second : c % 2 = d % 2) :
    (a + c) % 2 = (b + d) % 2 := by
  calc
    _ = (a % 2 + c % 2) % 2 := Nat.add_mod _ _ _
    _ = (b % 2 + d % 2) % 2 := by rw [first, second]
    _ = _ := (Nat.add_mod _ _ _).symm

/-- Every old higher generator preserves swap-count parity, including
surrounding contexts. No pasting in this finite syntax can change it. -/
theorem ExchangeHigher.swapParity (signature : Op → Interface Slot) {one two : List Op}
    {first second : Exchange signature one two} (cell : ExchangeHigher signature first second) :
    first.swapCount signature % 2 = second.swapCount signature % 2 := by
  induction cell with
  | refl => rfl
  | involution =>
      simp only [swapTwice_count, Exchange.swapCount]
  | braid => rfl
  | far => rfl
  | symm cell ih => exact ih.symm
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond
  | comp first second ihFirst ihSecond => exact add_parity ihFirst ihSecond
  | whisker past future cell ih => simpa only [Exchange.swapCount_whisker] using ih

namespace HigherBoundary

def readOnly (_ : Unit) : Interface Unit := ⟨∅, ∅⟩

def selfSwap : Exchange readOnly [(), ()] [(), ()] := .swap [] [] () () (by decide)
def identityPath : Exchange readOnly [(), ()] [(), ()] := .refl [(), ()]

theorem self_count : selfSwap.swapCount readOnly = 1 := rfl
theorem identity_count : identityPath.swapCount readOnly = 0 := rfl

/-- Three old higher forms are insufficient for contractibility of all paths
in the ACTUAL language, which permits repeated operation identifiers. -/
theorem no_self_contraction : ¬ Nonempty (ExchangeHigher readOnly selfSwap identityPath) := by
  rintro ⟨cell⟩
  have parity := cell.swapParity readOnly
  change (1 : Nat) = 0 at parity
  exact Nat.one_ne_zero parity

theorem three_forms_incomplete :
    ∃ (diagram : List Unit) (one two : Exchange readOnly diagram diagram),
      ¬ Nonempty (ExchangeHigher readOnly one two) :=
  ⟨[(), ()], selfSwap, identityPath, no_self_contraction⟩

/-- info: (true, 1, 0) -/
#guard_msgs in
#eval (checkExchange readOnly () (), selfSwap.swapCount readOnly, identityPath.swapCount readOnly)

end HigherBoundary
end CryptoOracle.StatefulDiagram
