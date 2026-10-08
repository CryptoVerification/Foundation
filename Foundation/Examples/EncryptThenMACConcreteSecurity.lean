import Foundation.Constructions.Symmetric.EncryptThenMAC.ConcreteSecurity
import Foundation.Examples.EncryptThenMACConcreteOperational

namespace Foundation.Symmetric.EncryptThenMAC.ConcreteSecurityExamples
open Foundation.Probability CryptoOracle ConcreteSecurity
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Randomize the requested row, then use its returned tag and another coin
to construct the candidate for the other ciphertext. -/
def adaptiveMAC (width : Nat) : Program Bool (Bits width) (Bool × Bits width) :=
  .coin fun request => .query request fun tag => .coin fun bit =>
    .done (!request, fun i => Bool.xor (tag i) bit)

theorem adaptive_queries (width : Nat) : (adaptiveMAC width).BoundedQueries 1 :=
  .coin _ 1 (fun request => .query request _ 0 (fun _ => .coin _ 0 (fun _ => .done _ 0)))

example (width : Nat → Nat) (n : Nat) :
    TableMAC.forgeryProbability width n (adaptiveMAC (width n)) ≤ tagGuessBound width n :=
  TableMAC.forgery_le width n _ (adaptive_queries (width n))

-- The bound is sharp, even for the fixed candidate with no signing query.
example (width : Nat → Nat) (n : Nat) :
    TableMAC.forgeryProbability width n (.done (false, fun _ => false)) = tagGuessBound width n :=
  TableMAC.done_forgery width n _

-- Width zero really gives success probability one, rather than an omitted case.
example : TableMAC.forgeryProbability (fun _ => 0) 0 (.done (false, fun i => Fin.elim0 i)) = 1 := by
  rw [TableMAC.done_forgery]
  norm_num

-- For the disclosed ciphertext, every fresh alternate tag fails verification.
example (width : Nat → Nat) (n : Nat) (request : Bool)
    (tag hidden candidateTag : Bits (width n)) :
    ¬macWins OneBitEncryption.scheme (TableMAC.scheme width)
      (TableMAC.rowKey request tag hidden) ((request, candidateTag), [(request, tag)]) := by
  classical
  cases request <;> simp [macWins, TableMAC.scheme, TableMAC.rowKey, TableMAC.sign, eq_comm]

/-- Two public requests are allowed, but exhaustion causes the second one to
fail. The candidate still depends on the first response and a private coin. -/
def repeatedIntegrity (width : Nat) :
    Program Bool (Option (Bool × Bits width)) (Bool × Bits width) :=
  .query false fun first => .query true fun _ => .coin fun bit =>
    .done (bit, fun i => Bool.xor ((first.map Prod.snd).getD (fun _ => false) i) bit)

example (width : Nat → Nat) (n : Nat) (key : Bool) :
    (reduceIntegrity OneBitEncryption.scheme (TableMAC.scheme width) key false
      (repeatedIntegrity (width n))).BoundedQueries 1 := TableMAC.reduction_queries width n key _

example (width : Nat → Nat) (n : Nat) :
    integrityAdvantage OneBitEncryption.scheme (TableMAC.scheme width) n
      (repeatedIntegrity (width n)) ≤ tagGuessBound width n := TableMAC.integrity_advantage width n _

/-- An adaptive second request may depend on a local coin, but the exhausted
state returns failure and preserves perfect privacy. -/
def repeatedPrivacy : Program (Bool × Bool) (Option Bool) Bool :=
  .query (false, true) fun first => .coin fun bit =>
    .query (bit, !bit) fun _ => .done (Bool.xor (first.getD false) bit)

example (n : Nat) : OneBitEncryption.programGame n false repeatedPrivacy =
    OneBitEncryption.programGame n true repeatedPrivacy := OneBitEncryption.program_perfect n _

example (n : Nat) : (encryptionGoal OneBitEncryption.scheme).advantage n ()
    (PMF.pure repeatedPrivacy) = 0 := OneBitEncryption.advantage_zero n _

-- Use the actual operational witness from the previous construction.
example (n : Nat) :
    (goal OneBitEncryption.scheme (TableMAC.scheme ConcreteOperationalExamples.width)).advantage n ()
      (ConcreteOperationalExamples.attacks n) ≤ tagGuessBound ConcreteOperationalExamples.width n :=
  (witness_security ConcreteOperationalExamples.width _ ConcreteOperationalExamples.sourceWitness n).1

example (n : Nat) := witness_security ConcreteOperationalExamples.width _
  ConcreteOperationalExamples.sourceWitness n

end Foundation.Symmetric.EncryptThenMAC.ConcreteSecurityExamples
