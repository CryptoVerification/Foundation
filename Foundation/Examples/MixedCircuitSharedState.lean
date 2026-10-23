import Foundation.Crypto.Logic.Polygraph.MixedCircuitStateful

/-! A single shared bit and its chronological read/write log. Copying a port
value keeps one state; independently restarting both children is distinguishable.
The example is a semantic boundary, not a new cryptographic security theorem. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.SharedState
set_option backward.isDefEq.respectTransparency false
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Foundation.Logic.Polygraph.StructuralTransport

abbrev Runtime := Bool × List (Bool × Bool)

abbrev signature : Signature Bool Unit Unit where
  PortAtom := Unit
  inputs _ := .unit
  outputs _ := .atom ()
  needs _ := ∅
  charges _ := 0

noncomputable def model : Stateful.Model signature (fun _ => True) (fun _ => Bool) Runtime where
  box operation _ state _ :=
    let response := if operation then state.1 else true
    PMF.pure ((if operation then state.1 else true, state.2 ++ [(operation, response)]), response)

def putThenRead : Circuit signature .unit (.pair (.atom ()) (.atom ())) :=
  .seq (.wire (.copy .unit)) (.tensor (.box false) (.box true))

def readThenPut : Circuit signature .unit (.pair (.atom ()) (.atom ())) :=
  .seq (.wire (.copy .unit))
    (.seq (.tensor (.box true) (.box false)) (.wire (.swap (.atom ()) (.atom ()))))

theorem putThenRead_needs : putThenRead.needs = ∅ := by
  simp only [putThenRead, Circuit.needs, signature, Finset.union_self]

theorem readThenPut_needs : readThenPut.needs = ∅ := by
  simp only [readThenPut, Circuit.needs, signature, Finset.union_self]

theorem putValid : Holds (fun _ => True) putThenRead.needs := fun _ _ => True.intro

theorem readValid : Holds (fun _ => True) readThenPut.needs := fun _ _ => True.intro

theorem shared_run (bit : Bool) (history : List (Bool × Bool)) :
    Stateful.evaluate model putThenRead putValid (bit, history) PUnit.unit =
      PMF.pure ((true, history ++ [(false, true), (true, true)]), (true, true)) := by
  simp [Stateful.evaluate, model, putThenRead, Wire.eval, List.append_assoc, PMF.pure_map]

theorem reversed_run (bit : Bool) (history : List (Bool × Bool)) :
    Stateful.evaluate model readThenPut readValid (bit, history) PUnit.unit =
      PMF.pure ((true, history ++ [(true, bit), (false, true)]), (true, bit)) := by
  simp [Stateful.evaluate, model, readThenPut, Wire.eval, List.append_assoc]

/-- The tempting fork starts the read again from the old state. -/
noncomputable def restarted (state : Runtime) : PMF (Bool × Bool) :=
  (model.box false (fun _ _ => True.intro) state PUnit.unit).bind fun left =>
    (model.box true (fun _ _ => True.intro) state PUnit.unit).map fun right => (left.2, right.2)

theorem restarted_run (bit : Bool) (history : List (Bool × Bool)) :
    restarted (bit, history) = PMF.pure (true, bit) := by
  simp [restarted, model, PMF.pure_map]

theorem shared_read_true (history : List (Bool × Bool)) :
    (Stateful.evaluate model putThenRead putValid (false, history) PUnit.unit).map (fun result => result.2.2) =
      PMF.pure true := by rw [shared_run, PMF.pure_map]

theorem restarted_read_false (history : List (Bool × Bool)) :
    (restarted (false, history)).map Prod.snd = PMF.pure false := by rw [restarted_run, PMF.pure_map]

theorem restart_not_shared (history : List (Bool × Bool)) :
    (Stateful.evaluate model putThenRead putValid (false, history) PUnit.unit).map Prod.snd ≠
      restarted (false, history) := by
  intro same
  have observed := congrArg (fun law : PMF (Bool × Bool) => law (true, true)) same
  simp [shared_run, PMF.pure_map, restarted_run, PMF.pure_apply] at observed

theorem unrestricted_exchange_false (history : List (Bool × Bool)) :
    Stateful.evaluate model putThenRead putValid (false, history) PUnit.unit ≠
      Stateful.evaluate model readThenPut readValid (false, history) PUnit.unit := by
  intro same
  have observed := congrArg (PMF.map (fun result : Runtime × (Bool × Bool) => result.2.2)) same
  rw [shared_run, reversed_run] at observed
  simp only [PMF.pure_map] at observed
  have value := congrArg (fun law : PMF Bool => law true) observed
  simp [PMF.pure_apply] at value

/-- Discard a port result while retaining the updated shared bit and full log. -/
def discardResult : Circuit signature .unit .unit := .seq putThenRead (.wire (.discard _))

theorem discardValid : Holds (fun _ => True) discardResult.needs := fun _ _ => True.intro

theorem discard_preserves_effects (bit : Bool) (history : List (Bool × Bool)) :
    Stateful.evaluate model discardResult discardValid (bit, history) PUnit.unit =
      PMF.pure ((true, history ++ [(false, true), (true, true)]), PUnit.unit) := by
  simp only [discardResult, Stateful.evaluate, shared_run, PMF.pure_bind, Wire.eval]

/-- Copy the already produced port value after a single effect. -/
def copyOnce : Circuit signature .unit (.pair (.atom ()) (.atom ())) :=
  .seq (.box false) (.wire (.copy (.atom ())))

/-- Copying the input before two boxes executes the effect twice. -/
def executeTwice : Circuit signature .unit (.pair (.atom ()) (.atom ())) :=
  .seq (.wire (.copy .unit)) (.tensor (.box false) (.box false))

theorem copyOnceValid : Holds (fun _ => True) copyOnce.needs := fun _ _ => True.intro

theorem executeTwiceValid : Holds (fun _ => True) executeTwice.needs := fun _ _ => True.intro

theorem copy_once_run (bit : Bool) (history : List (Bool × Bool)) :
    Stateful.evaluate model copyOnce copyOnceValid (bit, history) PUnit.unit =
      PMF.pure ((true, history ++ [(false, true)]), (true, true)) := by
  simp [copyOnce, Stateful.evaluate, model, Wire.eval]

theorem execute_twice_run (bit : Bool) (history : List (Bool × Bool)) :
    Stateful.evaluate model executeTwice executeTwiceValid (bit, history) PUnit.unit =
      PMF.pure ((true, history ++ [(false, true), (false, true)]), (true, true)) := by
  simp [executeTwice, Stateful.evaluate, model, Wire.eval, PMF.pure_map, List.append_assoc]

theorem copying_effect_not_value (bit : Bool) (history : List (Bool × Bool)) :
    Stateful.evaluate model copyOnce copyOnceValid (bit, history) PUnit.unit ≠
      Stateful.evaluate model executeTwice executeTwiceValid (bit, history) PUnit.unit := by
  intro same
  have lengths := congrArg (PMF.map (fun result : Runtime × (Bool × Bool) => result.1.2.length)) same
  rw [copy_once_run, execute_twice_run] at lengths
  simp only [PMF.pure_map, List.length_append, List.length_cons, List.length_nil] at lengths
  have one := congrArg (fun law : PMF Nat => law (history.length + 1)) lengths
  simp [PMF.pure_apply] at one

end CryptoLogic.Polygraph.MixedCircuit.Examples.SharedState
