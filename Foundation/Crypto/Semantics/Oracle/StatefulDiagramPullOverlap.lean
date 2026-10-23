import Foundation.Crypto.Semantics.Oracle.StatefulDiagramPullCells
import Mathlib.Tactic.FailIfNoProgress

/-! The overlapping front-swap/head-pull comparison, constructed from earlier
bounded cells. A head extraction is not introduced as a higher generator. -/
set_option backward.isDefEq.respectTransparency false
namespace CryptoOracle.StatefulDiagram
variable {Slot Op : Type} [DecidableEq Slot] [DecidableEq Op]

private theorem heq_cast_left {A B C : Type} (equal : A = B) (value : A) (other : C) :
    HEq (cast equal value) other ↔ HEq value other :=
  ⟨fun same => (cast_heq equal value).symm.trans same, fun same => (cast_heq equal value).trans same⟩

omit [DecidableEq Op] in
private theorem prepend_cast_heq (signature : Op → Interface Slot) (head : Op)
    {a b c d : List Op} (source : a = c) (target : b = d)
    (equal : Exchange signature a b = Exchange signature c d) (path : Exchange signature a b)
    {Other : Type} (other : Other) :
    HEq ((cast equal path).prepend signature head) other ↔ HEq (path.prepend signature head) other := by
  cases source
  cases target
  rfl

omit [DecidableEq Op] in
private theorem trans_heq (signature : Op → Interface Slot) {a b c a' b' c' : List Op}
    {p : Exchange signature a b} {q : Exchange signature b c}
    {p' : Exchange signature a' b'} {q' : Exchange signature b' c'}
    (source : a = a') (middle : b = b') (target : c = c') (first : HEq p p') (second : HEq q q') :
    HEq (p.trans q) (p'.trans q') := by
  cases source
  cases middle
  cases target
  cases eq_of_heq first
  cases eq_of_heq second
  rfl

omit [DecidableEq Op] in
private theorem prepend_heq (signature : Op → Interface Slot) (head : Op) {a b c d : List Op}
    {p : Exchange signature a b} {q : Exchange signature c d} (source : a = c) (target : b = d)
    (same : HEq p q) : HEq (p.prepend signature head) (q.prepend signature head) := by
  cases source
  cases target
  cases eq_of_heq same
  rfl

omit [DecidableEq Op] in
private theorem refl_heq (signature : Op → Interface Slot) {one two : List Op} (equal : one = two) :
    HEq (Exchange.refl (signature := signature) one) (Exchange.refl (signature := signature) two) := by
  cases equal
  rfl

omit [DecidableEq Op] in
private theorem swap_heq (signature : Op → Interface Slot) {past future past' future' : List Op} (a b : Op)
    (accepted accepted' : checkExchange signature a b = true) (before : past = past') (after : future = future') :
    HEq (Exchange.swap past future a b accepted) (Exchange.swap past' future' a b accepted') := by
  cases before
  cases after
  rfl

/-- Naturality square for a path and the selected first occurrence. -/
def PullSquare (signature : Op → Interface Slot) (wanted : Op) {one two : List Op}
    (path : Exchange signature one two) (source : AccessibleHead signature wanted one)
    (target : AccessibleHead signature wanted two) : Type :=
  HorizontalCoherence signature
    (.trans path (pullHead signature wanted two target))
    (.trans (pullHead signature wanted one source) ((path.eraseData signature wanted).prepend signature wanted))

attribute [local simp] heq_cast_left prepend_cast_heq pullHead frontSwap Exchange.eraseData eraseSwap
  Exchange.prepend List.erase_cons

set_option maxHeartbeats 1000000 in
/-- Every front-swap overlap, including one or both swapped IDs equal to the
wanted ID and extraction from arbitrarily far inside the common suffix. -/
def frontPullSquare (signature : Op → Interface Slot) (wanted a b : Op) (future : List Op)
    (ab : checkExchange signature a b = true)
    (source : AccessibleHead signature wanted (a :: b :: future))
    (target : AccessibleHead signature wanted (b :: a :: future)) :
    PullSquare signature wanted (frontSwap signature a b future ab) source target := by
  by_cases first : a = wanted
  · subst a
    by_cases second : b = wanted
    · subst b
      let p := frontSwap signature wanted wanted future ab
      have cell : HorizontalCoherence signature (p.trans (.refl _)) ((Exchange.refl _).trans (.refl _)) :=
        (HorizontalCoherence.base (ExchangeCoherence.rightUnit p)).trans
          ((frontSelf signature wanted future ab).trans
            (HorizontalCoherence.base (ExchangeCoherence.leftUnit (Exchange.refl _))).symm)
      unfold PullSquare
      convert cell using 1 <;> simp [p]
      all_goals
        repeat' first
        | exact HEq.rfl
        | apply trans_heq signature
        | apply prepend_heq signature
        | apply swap_heq signature
        | apply refl_heq signature
        | fail_if_no_progress simp_all
    · have ba := checkExchange_reverse signature wanted b ab
      let p := frontSwap signature wanted b future ab
      let q := frontSwap signature b wanted future ba
      have cell : HorizontalCoherence signature (p.trans ((Exchange.refl _).trans q))
          ((Exchange.refl _).trans (.refl _)) :=
        (HorizontalCoherence.comp (.refl p) (.base (.leftUnit q))).trans
          ((frontInvolution signature wanted b future ab ba).trans
            (HorizontalCoherence.base (ExchangeCoherence.leftUnit (Exchange.refl _))).symm)
      unfold PullSquare
      convert cell using 1 <;> simp [second, p, q]
      all_goals
        repeat' first
        | exact HEq.rfl
        | apply trans_heq signature
        | apply prepend_heq signature
        | apply swap_heq signature
        | apply refl_heq signature
        | fail_if_no_progress simp_all
  · by_cases second : b = wanted
    · subst b
      let p := frontSwap signature a wanted future ab
      have cell : HorizontalCoherence signature (p.trans (.refl _))
          (((Exchange.refl _).trans p).trans (.refl _)) :=
        (HorizontalCoherence.base (ExchangeCoherence.rightUnit p)).trans
          ((HorizontalCoherence.base (ExchangeCoherence.rightUnit ((Exchange.refl _).trans p))).trans
            (.base (.leftUnit p))).symm
      unfold PullSquare
      convert cell using 1 <;> simp [first, p]
      all_goals
        repeat' first
        | exact HEq.rfl
        | apply trans_heq signature
        | apply prepend_heq signature
        | apply swap_heq signature
        | apply refl_heq signature
        | fail_if_no_progress simp_all
    · have afterA := source.resolve_left first
      have afterB := afterA.2.resolve_left second
      have ah := afterA.1
      have bh := afterB.1
      let tail := future.erase wanted
      let r := pullHead signature wanted future afterB.2
      let p := frontSwap signature a b future ab
      let rab := (r.prepend signature b).prepend signature a
      let rba := (r.prepend signature a).prepend signature b
      let t := frontSwap signature a b (wanted :: tail) ab
      let u := (frontSwap signature a wanted tail ah).prepend signature b
      let v := frontSwap signature b wanted (a :: tail) bh
      let x := (frontSwap signature b wanted tail bh).prepend signature a
      let y := frontSwap signature a wanted (b :: tail) ah
      let z := (frontSwap signature a b tail ab).prepend signature wanted
      have cross : HorizontalCoherence signature (p.trans rba) (rab.trans t) :=
        (frontSwap_tail signature a b ab r).symm
      have braid : HorizontalCoherence signature (t.trans (u.trans v)) (x.trans (y.trans z)) :=
        frontBraid signature a b wanted tail ab ah bh
      have cell : HorizontalCoherence signature (p.trans ((rba.trans u).trans v))
          (((rab.trans x).trans y).trans z) :=
        (HorizontalCoherence.comp (.refl p) (.base (.assoc rba u v))).trans
          ((HorizontalCoherence.assoc signature p rba (u.trans v)).symm.trans
            ((HorizontalCoherence.comp cross (.refl (u.trans v))).trans
              ((HorizontalCoherence.assoc signature rab t (u.trans v)).trans
                ((HorizontalCoherence.comp (.refl rab) braid).trans
                  ((HorizontalCoherence.assoc signature rab x (y.trans z)).symm.trans
                    (HorizontalCoherence.assoc signature (rab.trans x) y z).symm)))))
      unfold PullSquare
      convert cell using 1 <;> simp [first, second, p, r, rab, rba, u, v, x, y, z, tail]
      all_goals
        repeat' first
        | exact HEq.rfl
        | apply trans_heq signature
        | apply prepend_heq signature
        | apply swap_heq signature
        | apply refl_heq signature
        | fail_if_no_progress simp_all

set_option maxHeartbeats 1000000 in
/-- Move the front-overlap comparison under any unchanged prefix. If the
wanted label occurs in that prefix, the extraction stops there. Otherwise
horizontal interchange moves the residual tail path past the head exchange. -/
def primitivePullSquare (signature : Op → Interface Slot) (wanted : Op) :
    (past future : List Op) → (a b : Op) → (ab : checkExchange signature a b = true) →
    (source : AccessibleHead signature wanted (past ++ [a, b] ++ future)) →
    (target : AccessibleHead signature wanted (past ++ [b, a] ++ future)) →
    PullSquare signature wanted (Exchange.swap past future a b ab) source target
  | [], future, a, b, ab, source, target => frontPullSquare signature wanted a b future ab source target
  | head :: past, future, a, b, ab, source, target => by
    by_cases equal : head = wanted
    · subst head
      let p := (Exchange.swap past future a b ab).prepend signature wanted
      have cell : HorizontalCoherence signature (p.trans (.refl _)) ((Exchange.refl _).trans p) :=
        (HorizontalCoherence.base (ExchangeCoherence.rightUnit p)).trans
          (HorizontalCoherence.base (ExchangeCoherence.leftUnit p)).symm
      unfold PullSquare
      convert cell using 1 <;> simp [p]
      all_goals
        repeat' first
        | exact HEq.rfl
        | apply trans_heq signature
        | apply prepend_heq signature
        | apply swap_heq signature
        | apply refl_heq signature
        | fail_if_no_progress simp_all
    · have sourceRest := source.resolve_left equal
      have targetRest := target.resolve_left equal
      let one := past ++ [a, b] ++ future
      let two := past ++ [b, a] ++ future
      let p := Exchange.swap past future a b ab
      let q := pullHead signature wanted two targetRest.2
      let r := pullHead signature wanted one sourceRest.2
      let e := eraseSwap signature wanted past future a b ab
      let pH := p.prepend signature head
      let qH := q.prepend signature head
      let rH := r.prepend signature head
      let eWH := (e.prepend signature wanted).prepend signature head
      let eHW := (e.prepend signature head).prepend signature wanted
      let f₀ := frontSwap signature head wanted (one.erase wanted) sourceRest.1
      let f₁ := frontSwap signature head wanted (two.erase wanted) sourceRest.1
      have lifted : HorizontalCoherence signature (pH.trans qH) (rH.trans eWH) := by
        simpa only [PullSquare, Exchange.prefix, Exchange.prepend, Exchange.eraseData, List.singleton_append,
          one, two, p, q, r, e, pH, qH, rH, eWH] using
          HorizontalCoherence.prefix [head]
            (primitivePullSquare signature wanted past future a b ab sourceRest.2 targetRest.2)
      have cross : HorizontalCoherence signature (eWH.trans f₁) (f₀.trans eHW) :=
        frontSwap_tail signature head wanted sourceRest.1 e
      have cell : HorizontalCoherence signature (pH.trans (qH.trans f₁)) ((rH.trans f₀).trans eHW) :=
        (HorizontalCoherence.assoc signature pH qH f₁).symm.trans
          ((HorizontalCoherence.comp lifted (.refl f₁)).trans
            ((HorizontalCoherence.assoc signature rH eWH f₁).trans
              ((HorizontalCoherence.comp (.refl rH) cross).trans
                (HorizontalCoherence.assoc signature rH f₀ eHW).symm)))
      unfold PullSquare
      convert cell using 1 <;> simp [equal, one, two, p, q, r, e, pH, qH, rH, eHW, f₀, f₁]
      all_goals
        repeat' first
        | exact HEq.rfl
        | apply trans_heq signature
        | apply prepend_heq signature
        | apply swap_heq signature
        | apply refl_heq signature
        | fail_if_no_progress simp_all

/-- A generated naturality square for every raw checked Exchange path. -/
def pullNaturality (signature : Op → Interface Slot) (wanted : Op) :
    {one two : List Op} → (path : Exchange signature one two) →
    (source : AccessibleHead signature wanted one) → (target : AccessibleHead signature wanted two) →
    PullSquare signature wanted path source target
  | word, _, .refl _, source, target => by
    let p := pullHead signature wanted word source
    simpa only [PullSquare, Exchange.eraseData, Exchange.prepend] using
      (HorizontalCoherence.base (ExchangeCoherence.leftUnit p)).trans
        (HorizontalCoherence.base (ExchangeCoherence.rightUnit p)).symm
  | _, _, .swap past future a b ab, source, target => primitivePullSquare signature wanted past future a b ab source target
  | _, _, .symm child, source, target => by
    simpa only [PullSquare, Exchange.eraseData, Exchange.prepend] using
      HorizontalCoherence.invertLeft signature (pullNaturality signature wanted child target source)
  | _, _, .trans first second, source, target => by
    let middle := (first.accessibleHead_iff signature wanted).mp source
    simpa only [PullSquare, Exchange.eraseData, Exchange.prepend] using
      HorizontalCoherence.composeSquares signature
        (pullNaturality signature wanted first source middle)
        (pullNaturality signature wanted second middle target)

end CryptoOracle.StatefulDiagram
