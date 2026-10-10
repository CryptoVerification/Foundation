import Foundation.Constructions.Symmetric.SecretPrefixMACReduction
import Foundation.Constructions.Hash.QueryIndifferentiability

/-! The same single-stage secret-prefix MAC with public compression access.
All three public windows and final verification share one world state. This
extends the attacker interface, without changing the existing hash/tag game. -/
namespace Foundation.Symmetric.SecretPrefixMAC

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev PublicRequest (κ n : Nat) := Request κ ⊕ Foundation.Hash.CompressionInput (Bits κ) (Bits n)
abbrev PublicAttack (κ n : Nat) := Program (PublicRequest κ n) (Tag n) (Message κ × Tag n)

/-- Hash, tag, and compression requests share the opaque two-window world.
Only tag requests add a message to the signed list. -/
noncomputable def publicOracle {κ n : Nat} {State : Type}
    (world : Oracle (Foundation.Hash.WorldInput (Bits κ) (Bits n)) (Tag n) State)
    (key : Key κ) : Oracle (PublicRequest κ n) (Tag n) (State × List (Message κ)) :=
  fun (state, signed) request => match request with
    | .inl (.inl message) => (world state (.inl message)).map fun answer => ((answer.1, signed), answer.2)
    | .inl (.inr message) => (world state (.inl (input key message))).map fun answer =>
        ((answer.1, message :: signed), answer.2)
    | .inr compression => (world state (.inr compression)).map fun answer => ((answer.1, signed), answer.2)

noncomputable def publicGame {κ n : Nat} {State : Type}
    (world : Oracle (Foundation.Hash.WorldInput (Bits κ) (Bits n)) (Tag n) State)
    (state : State) (messageLimit : Nat) (attack : PublicAttack κ n) : ProbComp Bool :=
  (keygen κ).bind fun key =>
    (attack.run (publicOracle world key) (state, [])).bind fun out =>
      (verify (Program.adaptOracle Sum.inl id world) key out.state.1 out.result.1 out.result.2).map fun answer =>
        answer.2 && decide (out.result.1 ∉ out.state.2) && decide (out.result.1.length ≤ messageLimit)

noncomputable def publicConstructedGame {κ n : Nat} (initial : Bits n) (terminal : Bits κ)
    (messageLimit : Nat) (attack : PublicAttack κ n) : ProbComp Bool :=
  publicGame (Foundation.Hash.realWorld initial terminal) [] messageLimit attack

/-- Separate public budgets, including every compression request. -/
inductive PublicBudget {κ n : Nat} (hashLength messageLength : Nat) :
    PublicAttack κ n → Nat → Nat → Nat → Prop where
  | done (result : Message κ × Tag n) (qH qT qC : Nat) :
      PublicBudget hashLength messageLength (.done result) qH qT qC
  | hash (message : Message κ) (next : Tag n → PublicAttack κ n) (qH qT qC : Nat)
      (length : message.length ≤ hashLength)
      (bound : ∀ response, PublicBudget hashLength messageLength (next response) qH qT qC) :
      PublicBudget hashLength messageLength (.query (.inl (.inl message)) next) (qH + 1) qT qC
  | sign (message : Message κ) (next : Tag n → PublicAttack κ n) (qH qT qC : Nat)
      (length : message.length ≤ messageLength)
      (bound : ∀ response, PublicBudget hashLength messageLength (next response) qH qT qC) :
      PublicBudget hashLength messageLength (.query (.inl (.inr message)) next) qH (qT + 1) qC
  | compression (input : Foundation.Hash.CompressionInput (Bits κ) (Bits n))
      (next : Tag n → PublicAttack κ n) (qH qT qC : Nat)
      (bound : ∀ response, PublicBudget hashLength messageLength (next response) qH qT qC) :
      PublicBudget hashLength messageLength (.query (.inr input) next) qH qT (qC + 1)
  | coin (next : Bool → PublicAttack κ n) (qH qT qC : Nat)
      (bound : ∀ bit, PublicBudget hashLength messageLength (next bit) qH qT qC) :
      PublicBudget hashLength messageLength (.coin next) qH qT qC

/-- The public compression window is a direct low-level query. Signing uses
the same high-level window with the secret key prepended. -/
def publicWorldProcedure {κ n : Nat} (key : Key κ) (signed : List (Message κ)) :
    PublicRequest κ n → Program (Foundation.Hash.WorldInput (Bits κ) (Bits n)) (Tag n) (List (Message κ) × Tag n)
  | .inl request => (hashProcedure key signed request).mapQueries Sum.inl id
  | .inr compression => .query (.inr compression) (fun response => .done (signed, response))

def publicDistinguisherKey {κ n : Nat} (key : Key κ) (messageLimit : Nat) (attack : PublicAttack κ n) :
    Program (Foundation.Hash.WorldInput (Bits κ) (Bits n)) (Tag n) Bool :=
  (Program.inlineState (publicWorldProcedure key) [] attack).bind
    (fun result => (checkProgram key messageLimit result).mapQueries Sum.inl id)

def publicDistinguisher {κ n : Nat} (messageLimit : Nat) (attack : PublicAttack κ n) :
    Program (Foundation.Hash.WorldInput (Bits κ) (Bits n)) (Tag n) Bool :=
  Program.sampleBitsWith κ (fun key => publicDistinguisherKey key messageLimit attack)

/-- Exact result law for any world, including the shared real compression
world and the candidate simulator's shared ideal world. -/
theorem publicDistinguisher_run {κ n : Nat} {State : Type}
    (world : Oracle (Foundation.Hash.WorldInput (Bits κ) (Bits n)) (Tag n) State)
    (state : State) (messageLimit : Nat) (attack : PublicAttack κ n) :
    ((publicDistinguisher messageLimit attack).run world state).map Outcome.result =
      publicGame world state messageLimit attack := by
  have projected (key : Key κ) :
      (attack.run (Program.statefulOracle (publicWorldProcedure key) world) ([], state)).map
        (Program.mapState Prod.swap) = attack.run (publicOracle world key) (state, []) := by
    apply Program.run_state_map
    intro source request
    cases request with
    | inl request => cases request <;>
        simp [Program.statefulOracle, publicWorldProcedure, hashProcedure, Program.mapQueries,
          Program.run, publicOracle, PMF.map_bind, PMF.pure_map] <;> rfl
    | inr compression =>
        simp [Program.statefulOracle, publicWorldProcedure, Program.run, publicOracle, PMF.map_bind, PMF.pure_map]
        rfl
  have compiled (key : Key κ) :
      ((Program.inlineState (publicWorldProcedure key) [] attack).run world state).map Program.resultState =
      (attack.run (publicOracle world key) (state, [])).map
        (fun out => (out.state.1, (out.state.2, out.result))) := by
    rw [Program.inlineState_run]
    have he := congrArg (PMF.map (fun out => (out.state.1, (out.state.2, out.result)))) (projected key)
    simpa only [PMF.map_comp, Program.mapState, Function.comp_def, Prod.swap] using he
  simp only [publicDistinguisher, Program.sampleBitsWith_run, PMF.map_bind, publicGame, keygen]
  congr 1
  funext key
  simp only [publicDistinguisherKey, Program.run_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have he := congrArg (fun law => law.bind (fun pair =>
    (((checkProgram key messageLimit pair.2).mapQueries Sum.inl id).run world pair.1).map Outcome.result))
    (compiled key)
  simp only [PMF.bind_map, Function.comp_def, Program.resultState] at he
  rw [he]
  congr 1
  funext out
  rw [Program.mapQueries_run_result]
  exact checkProgram_run (Program.adaptOracle Sum.inl id world) key messageLimit (out.state.2, out.result) out.state.1

/-- The one-stage reduction counts all public windows and its final check.
The input-length bound is only needed for the high-level hash window. -/
theorem PublicBudget.distinguisher_bound {κ n hashLength messageLength qH qT qC : Nat}
    {attack : PublicAttack κ n} (budget : PublicBudget hashLength messageLength attack qH qT qC)
    (messageLimit blockLimit : Nat) (positive : 1 ≤ blockLimit)
    (hashBlocks : hashLength + 1 ≤ blockLimit)
    (signBlocks : messageLength + 2 ≤ blockLimit)
    (finalBlocks : messageLimit + 2 ≤ blockLimit) :
    Foundation.Hash.WorldBound blockLimit (publicDistinguisher messageLimit attack) (qH + qT + qC + 1) := by
  have compiled (key : Key κ) (signed : List (Message κ)) :
      Foundation.Hash.WorldBound blockLimit
        ((Program.inlineState (publicWorldProcedure key) signed attack).bind
          (fun result => (checkProgram key messageLimit result).mapQueries Sum.inl id)) (qH + qT + qC + 1) := by
    induction budget generalizing signed with
    | done result qH qT qC =>
        simp only [Program.inlineState, Program.bind, checkProgram]
        split
        · rename_i valid
          simp only [Program.mapQueries, id_eq]
          apply Foundation.Hash.WorldBound.mono (q := 1) ?_ (by omega)
          apply Foundation.Hash.WorldBound.hash _ _ 0 ?_ (fun _ => .done _ 0)
          simp only [input, List.length_cons]
          omega
        · exact .done _ _
    | hash message next qH qT qC length bounds ih =>
        simp only [Program.inlineState, publicWorldProcedure, hashProcedure, Program.bind, Program.mapQueries, id_eq]
        have h := Foundation.Hash.WorldBound.hash message _ (qH + qT + qC + 1)
          (by omega) (fun response => ih response signed)
        convert h using 1; omega
    | sign message next qH qT qC length bounds ih =>
        simp only [Program.inlineState, publicWorldProcedure, hashProcedure, Program.bind, Program.mapQueries, id_eq]
        have h := Foundation.Hash.WorldBound.hash (input key message) _ (qH + qT + qC + 1)
          (by simp only [input, List.length_cons]; omega) (fun response => ih response (message :: signed))
        convert h using 1; omega
    | compression compression next qH qT qC bounds ih =>
        simp only [Program.inlineState, publicWorldProcedure, Program.bind]
        have h := Foundation.Hash.WorldBound.compression compression _ (qH + qT + qC + 1)
          positive (fun response => ih response signed)
        convert h using 1; omega
    | coin next qH qT qC bounds ih => exact .coin _ _ (fun bit => ih bit signed)
  have sampleBound {width : Nat}
      (next : Bits width → Program (Foundation.Hash.WorldInput (Bits κ) (Bits n)) (Bits n) Bool)
      (bound : ∀ key, Foundation.Hash.WorldBound blockLimit (next key) (qH + qT + qC + 1)) :
      Foundation.Hash.WorldBound blockLimit (Program.sampleBitsWith width next) (qH + qT + qC + 1) := by
    induction width with
    | zero => exact bound _
    | succ width ih => exact .coin _ _ (fun bit => ih _ (fun bits => bound (Fin.snoc bits bit)))
  exact sampleBound _ (fun key => compiled key [])

end Foundation.Symmetric.SecretPrefixMAC
