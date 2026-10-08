import Foundation.Constructions.Symmetric.OneTimePad
import Foundation.Crypto.Semantics.Oracle.QuerySecurity

/-! Finite-domain pseudorandom-function experiments. A key is sampled once
per real experiment; a complete function table is sampled once per ideal
experiment. Repeated requests therefore have consistent answers in both
worlds. These definitions count typed queries; a whole-machine resource
adapter must additionally certify the executable implementation. -/
namespace Foundation.Symmetric.PRF

open Foundation.Probability CryptoOracle
open scoped ENNReal

structure Scheme where
  Key : Nat → Type
  Domain : Nat → Type
  domainFinite : ∀ n, Fintype (Domain n)
  length : Nat → Nat
  keygen : ∀ n, ProbComp (Key n)
  evaluate : ∀ n, Key n → Domain n → Bits (length n)

abbrev Attack (S : Scheme) (n : Nat) := Program (S.Domain n) (Bits (S.length n)) Bool

/-- The hidden table is constant throughout an adaptive execution. -/
noncomputable def tableOracle {D : Type} {length : Nat} (table : D → Bits length) :
    Oracle D (Bits length) Unit := fun _ x => PMF.pure ((), table x)

noncomputable def runTable {D : Type} {length : Nat}
    (attack : Program D (Bits length) Bool) (table : D → Bits length) : ProbComp Bool :=
  (attack.run (tableOracle table) ()).map Outcome.result

noncomputable def real (S : Scheme) (n : Nat) (attack : Attack S n) : ProbComp Bool :=
  (S.keygen n).bind fun key => runTable attack (S.evaluate n key)

/-- Sampling the whole finite table is a semantic definition, not an
algorithm executed by the reduction or charged as a machine instruction. -/
noncomputable def ideal (S : Scheme) (n : Nat) (attack : Attack S n) : ProbComp Bool := by
  classical
  letI := S.domainFinite n
  exact (uniform (S.Domain n → Bits (S.length n))).bind (runTable attack)

noncomputable def goal (S : Scheme) : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun n _ => Attack S n
  advantage := fun n _ attack => probabilityGap
    (eventProb (real S n attack) (· = true))
    (eventProb (ideal S n attack) (· = true))

def queryClass (S : Scheme) (q : Nat → Nat) : AdversaryClass (goal S) where
  admissible _ A := ∀ n, (A n).BoundedQueries (q n)

/-- Query-only security; this does not assert a CPU time bound. -/
def QuerySecure (S : Scheme) (q : Nat → Nat) (ε : Nat → ℝ≥0∞) : Prop :=
  BoundedByOnWithin (goal S) (queryClass S q) (fun _ => ()) ε

/-- With no queries, neither the sampled key nor the sampled table affects
an attack's output, even when the attack uses local coins. -/
theorem zero_queries (S : Scheme) (n : Nat) (attack : Attack S n)
    (h : attack.BoundedQueries 0) : real S n attack = ideal S n attack := by
  classical
  have hr (table : S.Domain n → Bits (S.length n)) :
      runTable attack table = runTable attack (fun _ _ => false) :=
    h.zero_run_result_eq (tableOracle table) (tableOracle (fun _ _ => false)) () ()
  have hf : runTable attack = (fun _ : S.Domain n → Bits (S.length n) =>
      runTable attack (fun _ _ => false)) := funext hr
  unfold real ideal
  conv_lhs =>
    arg 2
    ext key
    rw [hr]
  conv_rhs => rw [hf]
  simp

/-- Both responses to a repeated input are the same fixed table entry. -/
theorem repeated_query {D : Type} {length : Nat} (table : D → Bits length) (x : D) :
    (Program.query x (fun first => Program.query x (fun second =>
      Program.done (first, second)))).run (tableOracle table) () =
    PMF.pure (⟨(table x, table x), (), [(x, table x), (x, table x)]⟩ :
      Outcome D (Bits length) (Bits length × Bits length) Unit) := by
  simp [Program.run, tableOracle, PMF.pure_map]

end Foundation.Symmetric.PRF
