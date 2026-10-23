import Foundation.Crypto.Semantics.Oracle.StatefulDiagramExchangeDecision

/-! A deterministic canonical word for checked exchange components.
Only labels present in the input are considered; exchange paths are not
enumerated. Global comparison of parallel proof terms by bounded higher
cells, and proof-size bounds, remain separate obligations. -/
namespace CryptoOracle.StatefulDiagram
variable {Slot Op Value : Type} [DecidableEq Slot] [LinearOrder Op]

/-- Distinct labels that the checked head scan can expose. -/
def availableHeads (signature : Op → Interface Slot) (word : List Op) : Finset Op :=
  word.toFinset.filter (fun wanted => (exposeHead signature wanted word).isSome = true)

private theorem accessible_mem (signature : Op → Interface Slot) (wanted : Op) (word : List Op)
    (accessible : AccessibleHead signature wanted word) : wanted ∈ word := by
  induction word with
  | nil => exact False.elim accessible
  | cons head tail ih =>
    rcases accessible with equal | ⟨_, rest⟩
    · simp [equal]
    · exact List.mem_cons_of_mem head (ih rest)

theorem mem_availableHeads (signature : Op → Interface Slot) (wanted : Op) (word : List Op) :
    wanted ∈ availableHeads signature word ↔ AccessibleHead signature wanted word := by
  simp only [availableHeads, Finset.mem_filter, List.mem_toFinset, exposeHead_success_iff]
  exact ⟨And.right, fun accessible => ⟨accessible_mem signature wanted word accessible, accessible⟩⟩

theorem availableHeads_nonempty (signature : Op → Interface Slot) (word : List Op) :
    (availableHeads signature word).Nonempty ↔ word ≠ [] := by
  cases word with
  | nil => simp [availableHeads]
  | cons head tail =>
    constructor
    · intro _; simp
    · intro _
      exact ⟨head, (mem_availableHeads signature head (head :: tail)).mpr (Or.inl rfl)⟩

/-- Every checked path preserves the complete finite set of available heads. -/
theorem Exchange.availableHeads_eq (signature : Op → Interface Slot) {one two : List Op}
    (path : Exchange signature one two) : availableHeads signature one = availableHeads signature two := by
  ext wanted
  simp only [mem_availableHeads]
  exact path.accessibleHead_iff signature wanted

/-- The least available label and a concrete path exposing it. -/
def leastHead (signature : Op → Interface Slot) (word : List Op)
    (nonempty : (availableHeads signature word).Nonempty) :
    HeadExtraction signature ((availableHeads signature word).min' nonempty) word :=
  (exposeHead signature ((availableHeads signature word).min' nonempty) word).get (by
    have member := Finset.min'_mem (availableHeads signature word) nonempty
    exact (exposeHead_success_iff signature _ word).mpr
      ((mem_availableHeads signature _ word).mp member))

/-- Fuel is a checked recursion parameter; the public normalizer supplies the
input length. A zero-fuel call returns its residual word unchanged. -/
def canonicalAux (signature : Op → Interface Slot) : Nat → List Op → List Op
  | 0, word => word
  | fuel + 1, word =>
    if nonempty : (availableHeads signature word).Nonempty then
      let selected := leastHead signature word nonempty
      (availableHeads signature word).min' nonempty :: canonicalAux signature fuel selected.rest
    else word

/-- A path exists even for partial normalization with insufficient fuel. -/
theorem canonicalAux_reachable (signature : Op → Interface Slot) (fuel : Nat) (word : List Op) :
    Nonempty (Exchange signature word (canonicalAux signature fuel word)) := by
  induction fuel generalizing word with
  | zero => exact ⟨.refl _⟩
  | succ fuel ih =>
    simp only [canonicalAux]
    split
    next nonempty =>
      obtain ⟨restPath⟩ := ih (leastHead signature word nonempty).rest
      exact ⟨(leastHead signature word nonempty).path.trans (by
        simpa only [List.singleton_append, List.append_nil] using
          restPath.whisker signature [(availableHeads signature word).min' nonempty] [])⟩
    next => exact ⟨.refl _⟩

/-- With enough fuel, any two exchange-related words have identical output.
The proof uses equal available-head sets and cancellation of the chosen head. -/
theorem canonicalAux_invariant (signature : Op → Interface Slot) (fuel : Nat)
    {one two : List Op} (enough : one.length ≤ fuel) (path : Exchange signature one two) :
    canonicalAux signature fuel one = canonicalAux signature fuel two := by
  induction fuel generalizing one two with
  | zero =>
    have first : one = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    have second : two = [] := List.length_eq_zero_iff.mp ((path.length_eq signature).symm.trans
      (List.length_eq_zero_iff.mpr first))
    subst one; subst two
    rfl
  | succ fuel ih =>
    have same := path.availableHeads_eq signature
    by_cases nonempty : (availableHeads signature one).Nonempty
    · have nonemptyTwo : (availableHeads signature two).Nonempty := same ▸ nonempty
      have chosen : (availableHeads signature one).min' nonempty =
          (availableHeads signature two).min' nonemptyTwo := by congr 1
      let first := leastHead signature one nonempty
      let second := leastHead signature two nonemptyTwo
      have tailReach : Nonempty (Exchange signature first.rest second.rest) := by
        have joint := first.path.symm.trans (path.trans second.path)
        have endpoint := congrArg (fun head => head :: second.rest) chosen.symm
        have corrected := Eq.mp (congrArg
          (Exchange signature ((availableHeads signature one).min' nonempty :: first.rest)) endpoint) joint
        exact corrected.cancel_head signature _
      obtain ⟨tailPath⟩ := tailReach
      have shorter : first.rest.length ≤ fuel := by
        have length := first.length signature _ one
        omega
      have residual := ih shorter tailPath
      simp only [canonicalAux, dif_pos nonempty, dif_pos nonemptyTwo]
      exact congrArg₂ List.cons chosen residual
    · have emptyOne : one = [] := by
        simpa only [availableHeads_nonempty, not_not] using nonempty
      have emptyTwo : two = [] := by
        apply List.length_eq_zero_iff.mp
        rw [← path.length_eq signature, emptyOne]
        rfl
      subst one; subst two
      rfl

/-- The public canonical word uses exactly the input length as fuel. -/
def canonicalWord (signature : Op → Interface Slot) (word : List Op) : List Op :=
  canonicalAux signature word.length word

theorem canonicalWord_reachable (signature : Op → Interface Slot) (word : List Op) :
    Nonempty (Exchange signature word (canonicalWord signature word)) :=
  canonicalAux_reachable signature word.length word

theorem Exchange.canonicalWord_eq (signature : Op → Interface Slot) {one two : List Op}
    (path : Exchange signature one two) : canonicalWord signature one = canonicalWord signature two := by
  unfold canonicalWord
  rw [← path.length_eq signature]
  exact canonicalAux_invariant signature one.length (Nat.le_refl _) path

/-- Equality of canonical words exactly characterizes the generated exchange
equivalence, without deciding arbitrary PMF equality. -/
theorem canonicalWord_complete (signature : Op → Interface Slot) (one two : List Op) :
    canonicalWord signature one = canonicalWord signature two ↔ Nonempty (Exchange signature one two) := by
  constructor
  · intro equal
    obtain ⟨first⟩ := canonicalWord_reachable signature one
    obtain ⟨second⟩ := canonicalWord_reachable signature two
    rw [← equal] at second
    exact ⟨first.trans second.symm⟩
  · rintro ⟨path⟩
    exact path.canonicalWord_eq signature

theorem canonicalWord_idempotent (signature : Op → Interface Slot) (word : List Op) :
    canonicalWord signature (canonicalWord signature word) = canonicalWord signature word := by
  obtain ⟨path⟩ := canonicalWord_reachable signature word
  exact (path.canonicalWord_eq signature).symm

/-- Execute the canonical word with the same kernels and initial store. -/
theorem canonicalWord_sound (signature : Op → Interface Slot) (word : List Op)
    (world : Kernels signature Value) (store : Store Slot Value) :
    execute signature world word store = execute signature world (canonicalWord signature word) store := by
  obtain ⟨path⟩ := canonicalWord_reachable signature word
  exact path.sound signature world store

/-- Prefix a single unchanged operation directly, avoiding append-unit casts
in recursively generated path data. -/
def Exchange.prepend (signature : Op → Interface Slot) (head : Op) : {one two : List Op} →
    Exchange signature one two → Exchange signature (head :: one) (head :: two)
  | _, _, .refl _ => .refl _
  | _, _, .swap past future a b accepted => .swap (head :: past) future a b accepted
  | _, _, .symm path => (path.prepend signature head).symm
  | _, _, .trans first second => (first.prepend signature head).trans (second.prepend signature head)

omit [LinearOrder Op] in
theorem Exchange.prepend_count (signature : Op → Interface Slot) (head : Op) {one two : List Op}
    (path : Exchange signature one two) : (path.prepend signature head).swapCount signature = path.swapCount signature := by
  induction path with
  | refl => rfl
  | swap => rfl
  | symm _ ih => exact ih
  | trans _ _ first second => exact congrArg₂ Nat.add first second

/-- Build the path during the same least-head recursion. This avoids invoking
an additional alignment search after computing the representative. -/
def canonicalAuxCertificate (signature : Op → Interface Slot) : (fuel : Nat) → (word : List Op) →
    Exchange signature word (canonicalAux signature fuel word)
  | 0, word => .refl word
  | fuel + 1, word => by
    unfold canonicalAux
    split
    next nonempty =>
      let selected := leastHead signature word nonempty
      let restPath := canonicalAuxCertificate signature fuel selected.rest
      exact selected.path.trans (restPath.prepend signature ((availableHeads signature word).min' nonempty))
    next => exact .refl word

/-- Executable path generation to the canonical word. -/
def canonicalCertificate (signature : Op → Interface Slot) (word : List Op) :
    Exchange signature word (canonicalWord signature word) :=
  canonicalAuxCertificate signature word.length word

/-- Canonicalization keeps the generated backwards input requirements. -/
theorem canonicalWord_dependencies (signature : Op → Interface Slot) (word : List Op) (needed : Finset Slot) :
    dependencies signature word needed = dependencies signature (canonicalWord signature word) needed :=
  (canonicalCertificate signature word).dependencies_eq signature needed

theorem canonicalWord_required (signature : Op → Interface Slot) (word : List Op) (needed : Finset Slot) :
    required signature word needed = required signature (canonicalWord signature word) needed :=
  (canonicalCertificate signature word).required_eq signature needed

theorem canonicalWord_obligations (signature : Op → Interface Slot) (word : List Op)
    (needed : Finset Slot) (changed : Finset Op) :
    obligations signature word needed changed =
      obligations signature (canonicalWord signature word) needed changed :=
  (canonicalCertificate signature word).obligations_eq signature needed changed

theorem canonicalWord_checkReuse (signature : Op → Interface Slot) (word : List Op)
    (needed : Finset Slot) (changed : Finset Op) :
    checkReuse signature word needed changed =
      checkReuse signature (canonicalWord signature word) needed changed := by
  simp only [checkReuse, canonicalWord_obligations signature word needed changed]

/-- The same local equality obligations repair the opposite corner: edit
kernels and canonicalize execution in either order, preserving the observation. -/
theorem canonicalWord_repair_across (signature : Op → Interface Slot) (word : List Op)
    (needed : Finset Slot) (changed : Finset Op) (old updated : Kernels signature Value)
    (unchanged : ∀ op ∉ changed, old op = updated op)
    (localLaws : ∀ op ∈ obligations signature word needed changed, old op = updated op)
    (store : Store Slot Value) :
    (execute signature old word store).map (view needed) =
      (execute signature updated (canonicalWord signature word) store).map (view needed) :=
  (canonicalCertificate signature word).repair_across signature needed changed old updated unchanged localLaws store

end CryptoOracle.StatefulDiagram
