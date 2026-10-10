import Foundation.Constructions.Hash.LatentGuessing

/-! Explicit finite-label capacity for the symbolic ideal experiment.
These are allocation and oracle-query bounds, not machine time or peak-space
certificates. Graph vertices are kept disjoint from the unused supply. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

local instance allocationCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance allocationLabelBEq : BEq Label := instBEqOfDecidableEq

local instance allocationGraphBEq : BEq ((Digest ⊕ Label) × Payload) := instBEqOfDecidableEq

/-- A reserved graph vertex cannot be allocated again from the remaining list. -/
def LatentState.AllocationValid (state : LatentState Payload Digest Label) : Prop :=
  state.supply.Nodup ∧ ∀ edge ∈ state.graph, edge.2 ∉ state.supply

/-- An operation uses at most cost labels. When that many labels are available,
it cannot change the overflow flag. Previously raised flags are not cleared. -/
structure AllocationBound (before after : LatentState Payload Digest Label) (cost : Nat) : Prop where
  valid : after.AllocationValid
  length : before.supply.length ≤ after.supply.length + cost
  overflow : cost ≤ before.supply.length → after.overflow = before.overflow

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem AllocationBound.refl (state : LatentState Payload Digest Label) (valid : state.AllocationValid) :
    AllocationBound state state 0 := ⟨valid, by omega, fun _ => rfl⟩

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem AllocationBound.mono {before after : LatentState Payload Digest Label} {cost larger : Nat}
    (bound : AllocationBound before after cost) (le : cost ≤ larger) : AllocationBound before after larger :=
  ⟨bound.valid, by have := bound.length; omega, fun available => bound.overflow (le.trans available)⟩

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem AllocationBound.trans {before middle after : LatentState Payload Digest Label} {left right : Nat}
    (first : AllocationBound before middle left) (last : AllocationBound middle after right) :
    AllocationBound before after (left + right) := by
  refine ⟨last.valid, ?_, ?_⟩
  · have := first.length
    have := last.length
    omega
  · intro available
    have nextAvailable : right ≤ middle.supply.length := by have := first.length; omega
    exact (last.overflow nextAvailable).trans (first.overflow (by omega))

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem AllocationBound.graph_cons {before after : LatentState Payload Digest Label} {cost : Nat}
    (bound : AllocationBound before after cost) (key : (Digest ⊕ Label) × Payload) (label : Label)
    (unused : label ∉ after.supply) :
    AllocationBound before { after with graph := (key, label) :: after.graph } cost := by
  refine ⟨⟨bound.valid.1, ?_⟩, bound.length, bound.overflow⟩
  intro edge member
  rcases List.mem_cons.mp member with rfl | member
  · exact unused
  · exact bound.valid.2 edge member

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem reserveLabel_allocation (state : LatentState Payload Digest Label) (valid : state.AllocationValid) :
    AllocationBound state (reserveLabel state).1 1 := by
  cases supply : state.supply with
  | nil =>
      simp only [reserveLabel, supply]
      refine ⟨⟨by simp, fun _ _ => by simp⟩, by simp [supply], ?_⟩
      intro available
      simp [supply] at available
  | cons label rest =>
      simp only [reserveLabel, supply]
      have nodup : (label :: rest).Nodup := supply ▸ valid.1
      refine ⟨⟨nodup.tail, ?_⟩, by simp [supply], fun _ => rfl⟩
      intro edge member inRest
      exact valid.2 edge member (by rw [supply]; exact List.mem_cons_of_mem _ inRest)

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem reserveLabel_selected_unused (state : LatentState Payload Digest Label)
    (valid : state.AllocationValid) (label : Label) (selected : (reserveLabel state).2 = some label) :
    label ∉ (reserveLabel state).1.supply := by
  cases supply : state.supply with
  | nil => simp [reserveLabel, supply] at selected
  | cons first rest =>
      simp only [reserveLabel, supply, Option.some.injEq] at selected
      subst label
      have nodup : (first :: rest).Nodup := supply ▸ valid.1
      simpa only [reserveLabel, supply] using (List.nodup_cons.mp nodup).1

omit [Fintype Digest] [Nonempty Digest] in
theorem latentAdvance_allocation (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : state.AllocationValid) (parent : Digest ⊕ Label) (block : Payload) :
    AllocationBound state (latentAdvance initial state parent block).1 1 := by
  unfold latentAdvance
  split
  · exact (AllocationBound.refl state valid).mono (by omega)
  · dsimp only
    split
    · rename_i child selected
      exact (reserveLabel_allocation state valid).graph_cons (parent, block) child
        (reserveLabel_selected_unused state valid child selected)
    · exact reserveLabel_allocation state valid

omit [Fintype Digest] [Nonempty Digest] in
theorem reserveMessage_allocation (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : state.AllocationValid) (parent : Digest ⊕ Label) (message : List Payload) :
    AllocationBound state (reserveMessage initial state parent message) message.length := by
  induction message generalizing state parent with
  | nil => exact AllocationBound.refl state valid
  | cons block rest ih =>
      have first := latentAdvance_allocation initial state valid parent block
      have last := ih (latentAdvance initial state parent block).1 first.valid (latentAdvance initial state parent block).2
      simpa only [reserveMessage, List.length_cons, Nat.add_comm] using first.trans last

omit [Fintype Digest] [Nonempty Digest] in
theorem chooseLatent_allocation (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : state.AllocationValid) (input : CompressionInput Payload Digest) :
    AllocationBound state (chooseLatent initial state input).1 1 := by
  unfold chooseLatent
  split
  · dsimp only
    split
    · split
      · exact (AllocationBound.refl state valid).mono (by omega)
      · exact reserveLabel_allocation state valid
    · split
      · rename_i child selected
        exact (reserveLabel_allocation state valid).graph_cons _ child
          (reserveLabel_selected_unused state valid child selected)
      · exact reserveLabel_allocation state valid
  · exact reserveLabel_allocation state valid

omit [Fintype Digest] [Nonempty Digest] in
theorem chooseLatent_selected_unused (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : state.AllocationValid) (input : CompressionInput Payload Digest) (label : Label)
    (selected : (chooseLatent initial state input).2 = some label) :
    label ∉ (chooseLatent initial state input).1.supply := by
  by_cases data : input.2.1 = false
  · simp only [chooseLatent, data, ↓reduceIte] at selected ⊢
    cases edge : state.graph.lookup (latentParent initial state input.1, input.2.2) with
    | some child =>
        simp only [edge] at selected ⊢
        by_cases pending : state.revealed.lookup child = none
        · simp only [pending, ↓reduceIte, Option.some.injEq] at selected ⊢
          subst label
          obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp edge
          apply valid.2 ((latentParent initial state input.1, input.2.2), child)
          rw [table]
          simp
        · simp only [pending, ↓reduceIte] at selected ⊢
          exact reserveLabel_selected_unused state valid label selected
    | none =>
        simp only [edge] at selected ⊢
        cases allocation : (reserveLabel state).2 with
        | none => simp [allocation] at selected
        | some child =>
            simp only [allocation, Option.some.injEq] at selected ⊢
            subst label
            exact reserveLabel_selected_unused state valid child allocation
  · simp only [chooseLatent, data] at selected ⊢
    exact reserveLabel_selected_unused state valid label selected

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Publication removes no additional supply labels: the selected label was
already reserved, or was a pending graph vertex outside the supply. -/
theorem finishLatent_allocation (state : LatentState Payload Digest Label) (valid : state.AllocationValid)
    (input : CompressionInput Payload Digest) (selected : Option Label) (output : Digest)
    (unused : ∀ label, selected = some label → label ∉ state.supply) :
    AllocationBound state (finishLatent state input selected output) 0 := by
  cases selected with
  | none => exact ⟨valid, by simp [finishLatent], fun _ => rfl⟩
  | some label =>
      have same : state.supply.filter (fun other => other != label) = state.supply := by
        apply List.filter_eq_self.mpr
        intro other member
        exact bne_iff_ne.mpr (fun eq => unused label rfl (eq ▸ member))
      simp only [finishLatent, same]
      exact ⟨valid, by simp, fun _ => rfl⟩

omit [Fintype Digest] [Nonempty Digest] in
theorem choose_finish_allocation (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : state.AllocationValid) (input : CompressionInput Payload Digest) (output : Digest) :
    AllocationBound state
      (finishLatent (chooseLatent initial state input).1 input (chooseLatent initial state input).2 output) 1 := by
  have choice := chooseLatent_allocation initial state valid input
  have finished := finishLatent_allocation _ choice.valid input (chooseLatent initial state input).2 output
    (fun label selected => chooseLatent_selected_unused initial state valid input label selected)
  simpa only [Nat.add_zero] using choice.trans finished

def latentRequestCost : WorldInput Payload Digest → Nat
  | .inl message => message.length
  | .inr _ => 1

/-- This bound follows actual supported transitions of the previously verified
world. Random outputs change no label-allocation arguments. -/
theorem latent_step_allocation (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (state : LatentWorldState Payload Digest Label) (valid : state.1.AllocationValid)
    (request : WorldInput Payload Digest) (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentWorld initial terminal hashOracle state request).support) :
    AllocationBound state.1 answer.1.1 (latentRequestCost request) := by
  rcases state with ⟨control, hashes, coordinates⟩
  dsimp only at valid ⊢
  rw [latentWorld_eq (hashOracle := hashOracle)] at support
  cases request with
  | inl message =>
      simp only at support
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨result, _, rfl⟩ := support
      exact reserveMessage_allocation initial control valid (.inl initial) message
  | inr input =>
      simp only at support
      cases cached : control.exposed.lookup input with
      | some output =>
          simp only [cached, PMF.mem_support_pure_iff] at support
          subst answer
          exact (AllocationBound.refl control valid).mono (by omega)
      | none =>
          simp only [cached] at support
          cases recognized : terminalMessage initial terminal control.exposed input with
          | some message =>
              simp only [recognized] at support
              rw [PMF.mem_support_map_iff] at support
              obtain ⟨result, _, rfl⟩ := support
              exact ⟨valid, by simp, fun _ => rfl⟩
          | none =>
              simp only [recognized] at support
              cases selected : (chooseLatent initial control input).2 with
              | none =>
                  simp only [selected] at support
                  rw [PMF.mem_support_map_iff] at support
                  obtain ⟨output, _, rfl⟩ := support
                  simpa only [selected, latentRequestCost] using choose_finish_allocation initial control valid input output
              | some label =>
                  simp only [selected] at support
                  rw [PMF.mem_support_map_iff] at support
                  obtain ⟨result, _, rfl⟩ := support
                  simpa only [selected, latentRequestCost] using choose_finish_allocation initial control valid input result.2

/-- A q-call interaction with at most blockLimit encoded blocks per call
allocates at most q*blockLimit labels, including all private data-path reserves. -/
theorem latent_run_allocation {Result : Type} {blockLimit q : Nat}
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload)
    (state : LatentWorldState Payload Digest Label) (valid : state.1.AllocationValid)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentWorld initial terminal hashOracle) state).support) :
    AllocationBound state.1 out.state.1 (q * blockLimit) := by
  induction bound generalizing state out with
  | done result q =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact (AllocationBound.refl state.1 valid).mono (Nat.zero_le _)
  | coin next q bound ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, reachable⟩ := support
      exact ih bit state valid out reachable
  | hash message next q length bound ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, reachable, rest⟩ := support
      rw [PMF.mem_support_map_iff] at rest
      obtain ⟨tail, ht, rfl⟩ := rest
      have first := latent_step_allocation initial terminal state valid (.inl message) answer reachable
      have last := ih answer.2 answer.1 first.valid tail ht
      apply (first.trans last).mono
      simp only [latentRequestCost, Nat.add_mul, Nat.one_mul]
      omega
  | compression input next q positive bound ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, reachable, rest⟩ := support
      rw [PMF.mem_support_map_iff] at rest
      obtain ⟨tail, ht, rfl⟩ := rest
      have first := latent_step_allocation initial terminal state valid (.inr input) answer reachable
      have last := ih answer.2 answer.1 first.valid tail ht
      apply (first.trans last).mono
      simp only [latentRequestCost, Nat.add_mul, Nat.one_mul]
      omega

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem latent_empty_allocation (supply : List Label) (nodup : supply.Nodup) :
    (LatentState.empty (Payload := Payload) (Digest := Digest) supply).AllocationValid :=
  ⟨nodup, fun _ member => False.elim (List.not_mem_nil member)⟩

/-- Explicit capacity suffices on every reachable outcome, with no probability
of label exhaustion and no extra ideal-oracle assumption. -/
theorem latent_no_overflow {Result : Type} {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup)
    (available : q * blockLimit ≤ supply.length)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentWorld initial terminal) (LatentState.empty supply, ([], []))).support) :
    out.state.1.overflow = false ∧ supply.length ≤ out.state.1.supply.length + q * blockLimit := by
  have resources := latent_run_allocation bound initial terminal _ (latent_empty_allocation supply nodup) out support
  exact ⟨resources.overflow available, resources.length⟩

/-- q*blockLimit distinct finite labels suffice. The enumerable supply is
concrete; the bound counts labels and does not measure encoded machine memory. -/
theorem latent_fin_capacity {Result : Type} {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest (Fin (q * blockLimit))))
    (support : out ∈ (attack.run (latentWorld initial terminal)
      (LatentState.empty (List.finRange (q * blockLimit)), ([], []))).support) :
    out.state.1.overflow = false := by
  exact (latent_no_overflow bound initial terminal (List.finRange (q * blockLimit))
    (List.nodup_finRange _) (by simp) out support).1


/-- The finite eager experiment has no overflow on any supported execution,
for every choice of its coordinate function. Uniform mixing has full support,
and its joint final-state law is exactly the lazy experiment's law. -/
theorem latent_eager_no_overflow [Fintype Label] {Result : Type} {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup)
    (available : q * blockLimit ≤ supply.length) (function : Label → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function))
      (LatentState.empty supply, ([], []))).support) :
    out.state.1.overflow = false := by
  have mixed : Program.resultState out ∈ ((uniform (Label → Digest)).bind (fun function =>
      (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function))
        (LatentState.empty supply, ([], []))).map Program.resultState)).support := by
    rw [PMF.mem_support_bind_iff]
    refine ⟨function, PMF.mem_support_uniformOfFintype function, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨out, support, rfl⟩
  rw [latent_eager_run] at mixed
  rw [PMF.mem_support_map_iff] at mixed
  obtain ⟨lazyOut, reachable, same⟩ := mixed
  have flag := (latent_no_overflow bound initial terminal supply nodup available lazyOut reachable).1
  have states : lazyOut.state = out.state := congrArg Prod.fst same
  rwa [states] at flag

/-- Choosing Label = Fin (q*blockLimit) removes the auxiliary cardinality
parameter from the online hidden-coordinate bound. This is still a bound for
the ideal experiment, not an indifferentiability theorem. -/
theorem latent_budgeted_online_guess_bound {Result : Type} {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) :
    eventProb ((uniform (Fin (q * blockLimit) → Digest)).bind (fun function =>
      (attack.run (Program.monitorOracle (latentGuessHit function)
        (latentCoordinateWorld initial terminal (RandomOracle.eager function)))
        ((LatentState.empty (List.finRange (q * blockLimit)), ([], [])), false)).map
          (fun out => out.state.2))) (· = true) ≤
      ((q * (q * blockLimit) : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simpa only [Fintype.card_fin] using latent_online_guess_bound initial terminal
    (List.finRange (q * blockLimit)) bound.queries

end Foundation.Hash
