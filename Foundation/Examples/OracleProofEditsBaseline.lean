import Foundation.Constructions.Symmetric.RandomFunctionMACProofSyntax

/-! Ordinary invariant/induction baseline for exactly the same complete-state
and posterior-law goals. Lemma sharing is unrestricted. This file neither
imports the elementary edit language nor uses generated edit certificates.
The known-coordinate invariant lemma is shared across all adaptive suffixes.
-/
namespace CryptoOracle.ProofEdits.Baseline
open Foundation.Probability Foundation.Symmetric.RandomFunctionMACProofEdits
set_option backward.isDefEq.respectTransparency false
variable {Input Tag Result : Type} [DecidableEq Input]

theorem compile_before_after [DecidableEq Tag] (attack : Program Input Tag (Input × Tag))
    (signed : List Input) : (before attack).compile signed = (after attack).compile signed := by
  induction attack generalizing signed with
  | done result => rcases result with ⟨message, guess⟩; rfl
  | query message next ih =>
      simp only [before, after, Command.compile]
      congr 1
      funext tag
      exact ih tag (signed ++ [message])
  | coin next ih =>
      simp only [before, after, Command.compile]
      congr 1
      funext bit
      exact ih bit signed

/-- One reusable ordinary proof, including arbitrary intervening queries and
history tests. No enumeration of response branches or edit orders is needed. -/
theorem remember_sound (p : Command Input Tag Result)
    (world : Oracle Input Tag (RandomOracle.Table Input Tag)) (laws : CacheLaws world)
    (signed : List Input) (table : RandomOracle.Table Input Tag) :
    p.run world signed table = p.remember.run world signed table := by
  induction p generalizing signed table with
  | done result => rfl
  | record message next ih => exact ih (signed ++ [message]) table
  | fresh message next ih => exact ih (decide (message ∉ signed)) signed table
  | coin next ih =>
      simp only [Command.run, Command.compile, Command.remember, Program.run]
      congr 1
      funext bit
      exact ih bit signed table
  | query message next ih =>
      simp only [Command.run, Command.compile, Command.remember, Program.run]
      apply bind_congr_of_support
      intro answer reachable
      exact congrArg (PMF.map (fun out =>
        { out with trace := (message, answer.2) :: out.trace }))
        ((next answer.2).recall_sound world laws message answer.2 signed answer.1
          (laws.stores table message answer reachable))

theorem cached_eq [DecidableEq Tag] (attack : Program Input Tag (Input × Tag))
    (world : Oracle Input Tag (RandomOracle.Table Input Tag)) (laws : CacheLaws world)
    (signed : List Input) (table : RandomOracle.Table Input Tag) :
    (before attack).run world signed table = (cached attack).run world signed table :=
  (congrArg (Program.run world table) (compile_before_after attack signed)).trans
    (remember_sound (after attack) world laws signed table)

theorem cached_posterior [DecidableEq Tag] [Fintype Input] [Fintype Tag] [Nonempty Tag]
    (attack : Program Input Tag (Input × Tag)) (signed : List Input)
    (table : RandomOracle.Table Input Tag) :
    (uniform (Input → Tag)).bind (fun function =>
      ((before attack).run (RandomOracle.eager function) signed table).map
        (fun out => (out, RandomOracle.complete table function))) =
    ((cached attack).run RandomOracle.oracle signed table).bind (fun out =>
      (uniform (Input → Tag)).map (fun function =>
        (out, RandomOracle.complete out.state function))) := by
  have sampling := RandomOracle.eager_lazy_complete ((before attack).compile signed) table
  change (uniform (Input → Tag)).bind (fun function =>
    ((before attack).run (RandomOracle.eager function) signed table).map
      (fun out => (out, RandomOracle.complete table function))) = _ at sampling
  rw [sampling]
  exact congrArg (fun law => law.bind (fun out =>
    (uniform (Input → Tag)).map (fun function =>
      (out, RandomOracle.complete out.state function))))
      (cached_eq attack RandomOracle.oracle lazy_cache_laws signed table)

end CryptoOracle.ProofEdits.Baseline
