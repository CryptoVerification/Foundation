import Foundation.Constructions.Symmetric.SecretPrefixMACKeyHit
import Foundation.Constructions.Hash.Indifferentiability
import Foundation.Crypto.Semantics.Oracle.BitSampling

/-! A syntactic, single-stage MAC-to-hash distinguisher. It checks the public
forgery conditions before its final oracle call, avoiding unbounded invalid
verification inputs. Equality is with the success law of the original game. -/
namespace Foundation.Symmetric.SecretPrefixMAC

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The signed-message list is private bookkeeping, not a second hash state. -/
def hashProcedure {κ n : Nat} (key : Key κ) (signed : List (Message κ)) :
    Request κ → Program (Message κ) (Tag n) (List (Message κ) × Tag n)
  | .inl message => .query message (fun response => .done (signed, response))
  | .inr message => .query (input key message)
      (fun response => .done (message :: signed, response))

def checkProgram {κ n : Nat} (key : Key κ) (messageLimit : Nat)
    (result : List (Message κ) × (Message κ × Tag n)) : Program (Message κ) (Tag n) Bool :=
  if result.2.1 ∉ result.1 ∧ result.2.1.length ≤ messageLimit then
    .query (input key result.2.1) (fun response => .done (decide (response = result.2.2)))
  else .done false

def hashDistinguisherKey {κ n : Nat} (key : Key κ) (messageLimit : Nat)
    (attack : Attack κ n) : Program (Message κ) (Tag n) Bool :=
  (Program.inlineState (hashProcedure key) [] attack).bind (checkProgram key messageLimit)

def hashDistinguisher {κ n : Nat} (messageLimit : Nat) (attack : Attack κ n) :
    Program (Message κ) (Tag n) Bool :=
  Program.sampleBitsWith κ (fun key => hashDistinguisherKey key messageLimit attack)

def worldDistinguisher {κ n : Nat} (messageLimit : Nat) (attack : Attack κ n) :
    Program (Foundation.Hash.WorldInput (Bits κ) (Bits n)) (Tag n) Bool :=
  (hashDistinguisher messageLimit attack).mapQueries Sum.inl id

/-- The private-state interpreter realizes the original MAC oracle after
swapping its bookkeeping and opaque hash-state components. -/
theorem hashProcedure_run {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ)
    (attack : Attack κ n) (state : State) (signed : List (Message κ)) :
    (attack.run (Program.statefulOracle (hashProcedure key) hash) (signed, state)).map
      (Program.mapState Prod.swap) = attack.run (oracle hash key) (state, signed) := by
  apply Program.run_state_map
  intro privateState request
  cases request <;>
    simp [Program.statefulOracle, hashProcedure, Program.run, oracle, tag,
      PMF.map_bind, PMF.pure_map]
  all_goals rfl

theorem compiled_attack_run {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ)
    (attack : Attack κ n) (state : State) (signed : List (Message κ)) :
    ((Program.inlineState (hashProcedure key) signed attack).run hash state).map
      Program.resultState =
    (attack.run (oracle hash key) (state, signed)).map
      (fun out => (out.state.1, (out.state.2, out.result))) := by
  rw [Program.inlineState_run]
  have he := congrArg (PMF.map (fun out => (out.state.1, (out.state.2, out.result))))
    (hashProcedure_run hash key attack state signed)
  simpa only [PMF.map_comp, Program.mapState, Function.comp_def, Prod.swap] using he

/-- Invalid final messages are rejected before hashing. This is equal to the
original verification success law even though final hidden states may differ. -/
theorem checkProgram_run {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ) (messageLimit : Nat)
    (result : List (Message κ) × (Message κ × Tag n)) (state : State) :
    ((checkProgram key messageLimit result).run hash state).map Outcome.result =
      (verify hash key state result.2.1 result.2.2).map (fun answer =>
        answer.2 && decide (result.2.1 ∉ result.1) &&
          decide (result.2.1.length ≤ messageLimit)) := by
  by_cases hf : result.2.1 ∉ result.1 ∧ result.2.1.length ≤ messageLimit
  · simp [checkProgram, hf, Program.run, verify, tag, PMF.map_bind, PMF.map_comp,
      Function.comp_def, PMF.pure_map]
    rfl
  · have hc : ∀ answer : State × Bool,
        (answer.2 && decide (result.2.1 ∉ result.1) &&
          decide (result.2.1.length ≤ messageLimit)) = false := by
      intro answer
      simp only [not_and_or] at hf
      rcases hf with hf | hf <;> simp [hf]
    simp only [checkProgram, hf, ↓reduceIte, Program.run, PMF.pure_map]
    simp_rw [hc]
    simp [PMF.map, Function.comp_def]

theorem hashDistinguisherKey_run {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (key : Key κ) (messageLimit : Nat)
    (attack : Attack κ n) (state : State) :
    ((hashDistinguisherKey key messageLimit attack).run hash state).map Outcome.result =
      (attack.run (oracle hash key) (state, [])).bind (fun outcome =>
        (verify hash key outcome.state.1 outcome.result.1 outcome.result.2).map (fun answer =>
          answer.2 && decide (outcome.result.1 ∉ outcome.state.2) &&
            decide (outcome.result.1.length ≤ messageLimit))) := by
  simp only [hashDistinguisherKey, Program.run_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  have he := congrArg (fun law => law.bind (fun pair =>
    ((checkProgram key messageLimit pair.2).run hash pair.1).map Outcome.result))
      (compiled_attack_run hash key attack state [])
  simp only [PMF.bind_map, Function.comp_def, Program.resultState] at he
  rw [he]
  congr 1
  funext outcome
  exact checkProgram_run hash key messageLimit (outcome.state.2, outcome.result) outcome.state.1

/-- The reduction is an actual oracle program with fair-coin key generation.
Its Boolean result law is exactly the original MAC game for every hash oracle. -/
theorem hashDistinguisher_run {κ n : Nat} {State : Type}
    (hash : Oracle (Message κ) (Tag n) State) (state : State) (messageLimit : Nat)
    (attack : Attack κ n) :
    ((hashDistinguisher messageLimit attack).run hash state).map Outcome.result =
      game hash state messageLimit attack := by
  simp only [hashDistinguisher, Program.sampleBitsWith_run, PMF.map_bind, game, keygen]
  congr 1
  funext key
  exact hashDistinguisherKey_run hash key messageLimit attack state

/-- Query accounting includes the final verification. A signing message
needs one extra key block, and every constructed hash adds its terminal block. -/
theorem Budget.compiled_worldBound {κ n hashLength messageLength qH qT : Nat}
    {attack : Attack κ n} (budget : Budget hashLength messageLength attack qH qT)
    (key : Key κ) (signed : List (Message κ)) (messageLimit blockLimit : Nat)
    (hashBlocks : hashLength + 1 ≤ blockLimit)
    (signBlocks : messageLength + 2 ≤ blockLimit)
    (finalBlocks : messageLimit + 2 ≤ blockLimit) :
    Foundation.Hash.WorldBound blockLimit
      (((Program.inlineState (hashProcedure key) signed attack).bind
        (checkProgram key messageLimit)).mapQueries Sum.inl id) (qH + qT + 1) := by
  induction budget generalizing signed with
  | done result qH qT =>
      simp only [Program.inlineState, Program.bind, checkProgram]
      split
      · rename_i hf
        simp only [Program.mapQueries, id_eq]
        apply Foundation.Hash.WorldBound.mono (q := 1) ?_ (by omega)
        apply Foundation.Hash.WorldBound.hash _ _ 0 ?_ (fun _ => .done _ 0)
        simp only [input, List.length_cons]
        omega
      · exact .done _ _
  | hash message next qH qT hl hb ih =>
      simp only [Program.inlineState, hashProcedure, Program.bind, Program.mapQueries, id_eq]
      have h := Foundation.Hash.WorldBound.hash message _ (qH + qT + 1)
        (show message.length + 1 ≤ blockLimit by omega) (fun response => ih response signed)
      simpa only [Nat.add_right_comm] using h
  | sign message next qH qT hl hb ih =>
      simp only [Program.inlineState, hashProcedure, Program.bind, Program.mapQueries, id_eq]
      have h := Foundation.Hash.WorldBound.hash (input key message) _ (qH + qT + 1)
        (show (input key message).length + 1 ≤ blockLimit by
          simp only [input, List.length_cons]
          omega) (fun response => ih response (message :: signed))
      simpa only [Nat.add_assoc] using h
  | coin next qH qT hb ih =>
      exact .coin _ _ (fun bit => ih bit signed)

private theorem sampleBitsWith_worldBound {width κ n : Nat} (blockLimit queries : Nat)
    (next : Bits width → Program (Foundation.Hash.WorldInput (Bits κ) (Bits n)) (Bits n) Bool)
    (bound : ∀ key, Foundation.Hash.WorldBound blockLimit (next key) queries) :
    Foundation.Hash.WorldBound blockLimit (Program.sampleBitsWith width next) queries := by
  induction width with
  | zero => exact bound _
  | succ κ ih =>
      exact .coin _ _ (fun bit => ih _ (fun key => bound (Fin.snoc key bit)))

private theorem sampleBitsWith_mapQueries {κ : Nat} {Source Target Response Result : Type}
    (encode : Source → Target) (next : Bits κ → Program Source Response Result) :
    (Program.sampleBitsWith κ next).mapQueries encode id =
      Program.sampleBitsWith κ (fun key => (next key).mapQueries encode id) := by
  induction κ with
  | zero => rfl
  | succ κ ih =>
      simp only [Program.sampleBitsWith, Program.mapQueries]
      congr 1
      funext bit
      exact ih _

theorem worldDistinguisher_bound {κ n hashLength messageLength qH qT : Nat}
    {attack : Attack κ n} (budget : Budget hashLength messageLength attack qH qT)
    (messageLimit blockLimit : Nat)
    (hashBlocks : hashLength + 1 ≤ blockLimit)
    (signBlocks : messageLength + 2 ≤ blockLimit)
    (finalBlocks : messageLimit + 2 ≤ blockLimit) :
    Foundation.Hash.WorldBound blockLimit (worldDistinguisher messageLimit attack)
      (qH + qT + 1) := by
  simp only [worldDistinguisher, hashDistinguisher, sampleBitsWith_mapQueries]
  apply sampleBitsWith_worldBound
  intro key
  exact budget.compiled_worldBound key [] messageLimit blockLimit hashBlocks signBlocks finalBlocks

noncomputable def constructedHash {κ n : Nat} (initial : Bits n) (terminal : Bits κ) :
    Oracle (Message κ) (Tag n) (Foundation.Hash.CompressionTable (Bits κ) (Bits n)) :=
  Program.implementedOracle (Foundation.Hash.prefixFreeMD initial terminal) RandomOracle.oracle

noncomputable def constructedGame {κ n : Nat} (initial : Bits n) (terminal : Bits κ)
    (messageLimit : Nat) (attack : Attack κ n) : ProbComp Bool :=
  game (constructedHash initial terminal) [] messageLimit attack

/-- Exactly the real-world experiment of the indifferentiability protocol. -/
theorem worldDistinguisher_real {κ n : Nat} (initial : Bits n) (terminal : Bits κ)
    (messageLimit : Nat) (attack : Attack κ n) :
    ((worldDistinguisher messageLimit attack).run
      (Foundation.Hash.realWorld initial terminal) []).map Outcome.result =
        constructedGame initial terminal messageLimit attack := by
  rw [worldDistinguisher, Program.mapQueries_run_result]
  have ho : Program.adaptOracle Sum.inl id (Foundation.Hash.realWorld initial terminal) =
      constructedHash initial terminal := by
    funext state request
    simp only [Program.adaptOracle, Foundation.Hash.realWorld, constructedHash,
      Program.implementedOracle, PMF.map_comp, Function.comp_def, id_eq]
    rfl
  rw [ho, hashDistinguisher_run]
  rfl

/-- Every simulator has the same high-only game here. Its private state is
preserved, and projection gives the ordinary shared ROM game exactly. -/
theorem worldDistinguisher_ideal {κ n : Nat}
    (simulator : Foundation.Hash.Simulator (Bits κ) (Bits n))
    (messageLimit : Nat) (attack : Attack κ n) :
    ((worldDistinguisher messageLimit attack).run
      (simulator.world RandomOracle.oracle) (simulator.initial, [])).map Outcome.result =
        romGame messageLimit attack := by
  rw [worldDistinguisher, Program.mapQueries_run_result]
  have hp := Program.run_state_map_result Prod.snd
    (Program.adaptOracle Sum.inl id (simulator.world RandomOracle.oracle))
    RandomOracle.oracle (by
      intro state request
      simp only [Program.adaptOracle, Foundation.Hash.Simulator.world, PMF.map_comp,
        Function.comp_def, id_eq]
      change PMF.map id _ = _
      exact PMF.map_id _)
    (hashDistinguisher messageLimit attack) (simulator.initial, [])
  rw [hp, hashDistinguisher_run]
  rfl

/-- Inlining the actual hash construction gives this explicit compression
call budget, including cached calls, the key block and final verification. -/
theorem reduction_compression_queries {κ n hashLength messageLength qH qT : Nat}
    {attack : Attack κ n} (budget : Budget hashLength messageLength attack qH qT)
    (initial : Bits n) (terminal : Bits κ) (messageLimit blockLimit : Nat)
    (hashBlocks : hashLength + 1 ≤ blockLimit)
    (signBlocks : messageLength + 2 ≤ blockLimit)
    (finalBlocks : messageLimit + 2 ≤ blockLimit) :
    (Foundation.Hash.expand initial terminal (worldDistinguisher messageLimit attack)).BoundedQueries
      ((qH + qT + 1) * blockLimit) :=
  (worldDistinguisher_bound budget messageLimit blockLimit hashBlocks signBlocks finalBlocks).expanded_queries
    initial terminal

/-- Conditional composition for the concrete single-stage MAC game whose
adversary has public hash and signing access. The fixed common simulator is
chosen by `indifferentiable`, before this reduction or any MAC adversary.
This theorem does not prove the missing hash indifferentiability bound and does
not yet grant the MAC adversary a separate public compression interface. -/
theorem constructed_security_of_indifferentiable
    {κ n hashLength messageLength qH qT blockLimit simulatorCalls : Nat}
    (initial : Bits n) (terminal : Bits κ) (messageLimit : Nat) (error : ℝ≥0∞)
    (attack : Attack κ n) (budget : Budget hashLength messageLength attack qH qT)
    (hashBlocks : hashLength + 1 ≤ blockLimit)
    (signBlocks : messageLength + 2 ≤ blockLimit)
    (finalBlocks : messageLimit + 2 ≤ blockLimit)
    (indifferentiable : Foundation.Hash.QueryIndifferentiable initial terminal blockLimit
      (qH + qT + 1) simulatorCalls error) :
    eventProb (constructedGame initial terminal messageLimit attack) (· = true) ≤
      qH * ((2 : ℝ≥0∞) ^ κ)⁻¹ + ((2 : ℝ≥0∞) ^ n)⁻¹ + error := by
  obtain ⟨simulator, _, secure⟩ := indifferentiable
  have hd := secure (worldDistinguisher messageLimit attack)
    (worldDistinguisher_bound budget messageLimit blockLimit hashBlocks signBlocks finalBlocks)
  change probabilityGap
    (eventProb (((worldDistinguisher messageLimit attack).run
      (Foundation.Hash.realWorld initial terminal) []).map Outcome.result) (· = true))
    (eventProb (((worldDistinguisher messageLimit attack).run
      (simulator.world RandomOracle.oracle) (simulator.initial, [])).map Outcome.result)
        (· = true)) ≤ error at hd
  rw [worldDistinguisher_real, worldDistinguisher_ideal] at hd
  have hOne : eventProb (constructedGame initial terminal messageLimit attack) (· = true) ≤
      error + successProbability messageLimit attack := by
    apply tsub_le_iff_right.mp
    exact (le_max_left _ _).trans hd
  calc
    _ ≤ error + successProbability messageLimit attack := hOne
    _ ≤ error + (qH * ((2 : ℝ≥0∞) ^ κ)⁻¹ + ((2 : ℝ≥0∞) ^ n)⁻¹) :=
      add_le_add (le_refl _) (rom_security_bits messageLimit attack budget)
    _ = _ := add_comm _ _

end Foundation.Symmetric.SecretPrefixMAC
