import Foundation.Constructions.Symmetric.SecretPrefixMACSimulatorMerge

/-! Concrete query and input-length growth for merging the compression
simulator into a ROM MAC attacker. Table search is host computation here;
these are syntactic call bounds, not CPU or encoded-memory certificates. -/
namespace Foundation.Symmetric.SecretPrefixMAC

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

/-- Increasing the two existing MAC query budgets preserves admissibility. -/
theorem Budget.mono_counts {κ n hashLength messageLength qH qT rH rT : Nat}
    {attack : Attack κ n} (budget : Budget hashLength messageLength attack qH qT)
    (hashes : qH ≤ rH) (tags : qT ≤ rT) : Budget hashLength messageLength attack rH rT := by
  induction budget generalizing rH rT with
  | done result qH qT => exact .done _ _ _
  | hash message next qH qT length bounds ih =>
      cases rH with
      | zero => omega
      | succ rH => exact .hash _ _ _ _ length (fun response => ih response (by omega) tags)
  | sign message next qH qT length bounds ih =>
      cases rT with
      | zero => omega
      | succ rT => exact .sign _ _ _ _ length (fun response => ih response hashes (by omega))
  | coin next qH qT bounds ih => exact .coin _ _ _ (fun bit => ih bit hashes tags)

/-- Fair-coin sampling adds no hash or tag queries to the existing budget. -/
theorem Budget.sampleBitsWith {κ n width hashLength messageLength qH qT : Nat}
    (next : Bits width → Attack κ n)
    (bound : ∀ bits, Budget hashLength messageLength (next bits) qH qT) :
    Budget hashLength messageLength (Program.sampleBitsWith width next) qH qT := by
  induction width with
  | zero => exact bound _
  | succ width ih => exact .coin _ _ _ (fun bit => ih _ (fun bits => bound (Fin.snoc bits bit)))

/-- The actual recognizer's returned message fits its table-length fuel,
even on malformed tables; no collision or path-uniqueness assumption is used. -/
theorem simulator_message_length {κ n : Nat} (initial : Bits n) (terminal : Bits κ)
    (table : Foundation.Hash.CompressionTable (Bits κ) (Bits n))
    (input : Foundation.Hash.CompressionInput (Bits κ) (Bits n)) (message : Message κ)
    (found : Foundation.Hash.terminalMessage initial terminal table input = some message) :
    message.length ≤ table.length := by
  unfold Foundation.Hash.terminalMessage at found
  split at found
  · exact (Foundation.Hash.messagePrefix_sound initial table table.length input.1 message found).2
  · cases found

/-- Every remaining compression request consumes at most one table entry
and adds at most one public hash call. Its recovered input has length bounded
by the number of compression entries accumulated so far. -/
theorem PublicBudget.merged_budget {κ n hashLength messageLength qH qT qC : Nat}
    {attack : PublicAttack κ n} (budget : PublicBudget hashLength messageLength attack qH qT qC)
    (initial : Bits n) (terminal : Bits κ)
    (table : Foundation.Hash.CompressionTable (Bits κ) (Bits n)) (totalCompression : Nat)
    (capacity : table.length + qC ≤ totalCompression) :
    Budget (max hashLength totalCompression) messageLength (mergeAttack initial terminal table attack) (qH + qC) qT := by
  induction budget generalizing table with
  | done result qH qT qC =>
      exact .done _ _ _
  | hash message next qH qT qC length bounds ih =>
      simp only [mergeAttack, Program.inlineState, mergeProcedure, Program.bind]
      have h := Budget.hash message _ (qH + qC) qT
        (length.trans (Nat.le_max_left _ _)) (fun response => ih response table capacity)
      simpa only [Nat.add_right_comm, mergeAttack] using h
  | sign message next qH qT qC length bounds ih =>
      simp only [mergeAttack, Program.inlineState, mergeProcedure, Program.bind]
      exact Budget.sign message _ (qH + qC) qT length (fun response => ih response table capacity)
  | coin next qH qT qC bounds ih =>
      exact .coin _ _ _ (fun bit => ih bit table capacity)
  | compression input next qH qT qC bounds ih =>
      cases cached : table.lookup input with
      | some output =>
          simp only [mergeAttack, Program.inlineState, mergeProcedure, Foundation.Hash.simulatorProgram,
            cached, Program.inline, Program.bind]
          exact (ih output table (by omega)).mono_counts (by omega) (le_refl _)
      | none =>
          cases found : Foundation.Hash.terminalMessage initial terminal table input with
          | some message =>
              simp only [mergeAttack, Program.inlineState, mergeProcedure, Foundation.Hash.simulatorProgram,
                cached, found, Program.inline, simulatorROMHandler, Program.bind]
              have length : message.length ≤ max hashLength totalCompression :=
                (simulator_message_length initial terminal table input message found).trans
                  (Nat.le_trans (by omega) (Nat.le_max_right _ _))
              have h := Budget.hash message _ (qH + qC) qT length
                (fun response => ih response ((input, response) :: table)
                  (by simp only [List.length_cons]; omega))
              simpa only [Nat.add_assoc, mergeAttack] using h
          | none =>
              simp only [mergeAttack, Program.inlineState, mergeProcedure, Foundation.Hash.simulatorProgram,
                cached, found, Program.inline, simulatorROMHandler, Program.sampleBitsWith_bind, Program.bind]
              apply Budget.sampleBitsWith
              intro output
              exact (ih output ((input, output) :: table)
                (by simp only [List.length_cons]; omega)).mono_counts (by omega) (le_refl _)

/-- Empty initial simulator state gives the explicit ROM attacker budgets:
qH+qC public hashes, qT tags, and public hash inputs of at most max(LH,qC) blocks. -/
theorem PublicBudget.merged_from_empty {κ n hashLength messageLength qH qT qC : Nat}
    {attack : PublicAttack κ n} (budget : PublicBudget hashLength messageLength attack qH qT qC)
    (initial : Bits n) (terminal : Bits κ) :
    Budget (max hashLength qC) messageLength (mergeAttack initial terminal [] attack) (qH + qC) qT :=
  budget.merged_budget initial terminal [] qC (by simp)

end Foundation.Symmetric.SecretPrefixMAC
