import Foundation.Constructions.Hash.PolygraphLookup

/-! Adaptive branching, a local coin and repeated requests under one common
exposure witness, followed by execution of the actual native lookup code. -/
namespace CryptoOracle.RandomOracle.PolygraphExamples

open Foundation.Probability Foundation.Symmetric
open CryptoOracle.Interactive

def probe : Program Bool Bool Bool := .coin fun coin =>
  .query false fun first =>
    .query (if coin then first else true) fun second =>
      .query false fun again => .done (again == first && second)

theorem probe_queries : probe.BoundedQueries 3 :=
  .coin _ 3 (fun _ => .query _ _ 2 (fun _ => .query _ _ 1
    (fun _ => .query _ _ 0 (fun _ => .done _ 0))))

theorem all_prefetches_same_public
    (a : Finset Bool → Outcome Bool Bool Bool (Cube.cube Bool Bool).State)
    (ha : a ∈ (Cube.executionJoint probe).support) (S T : Finset Bool) :
    (a S).result = (a T).result ∧ (a S).trace = (a T).trace :=
  Cube.execution_public probe a ha S T

noncomputable def exact_prefetch :
    CryptoLogic.Polygraph.Experiment.ExactPath
      (.sample (Cube.publicLaw probe Finset.univ))
      (.sample ((probe.run oracle []).map (fun out => (out.result, out.trace)))) :=
  Cube.prefetchPath probe Finset.univ

theorem lazy_marginal : (Cube.coupled probe).map Prod.fst = probe.run oracle [] :=
  Cube.coupled_lazy probe

/-- info: ([some false, some true], [some false, some true], 2, 3) -/
#guard_msgs in
#eval
  let c := Cube.cube Bool Bool
  let root : c.State := (∅, id)
  let left := c.run [false, true] root
  let right := c.run [true, false, false] root
  ([false, true].map (Cube.view left), [false, true].map (Cube.view right),
    right.1.card, (c.runCount [true, false, false] root).2)

namespace Native

open Foundation.Hash Foundation.Hash.Native.SimulatorLookup

def zero : Bits 1 := fun _ => false
def one : Bits 1 := fun _ => true
def first : CompressionInput (Bits 1) (Bits 1) := (zero, (false, zero))
def second : CompressionInput (Bits 1) (Bits 1) := (one, (true, one))
def left : CompressionTable (Bits 1) (Bits 1) := [(first, zero), (second, one)]
def right : CompressionTable (Bits 1) (Bits 1) := left.reverse

def execute (table : CompressionTable (Bits 1) (Bits 1)) (fuel : Nat) :=
  let start := NativeCode.frame () [] (scanStart table first [] [])
  let result := Reification.simulate (lookupCode 1 1) (fun state _ => (state, []))
    false fuel start
  (Reification.packet result.1.control, result.2)

-- Different layouts have the same response, with genuinely different times.
-- One step before each first halt there is no completed packet.
/-- info: true -/
#guard_msgs in
#eval
  [execute left 200 == (some [false, false, false, true, false], 38),
   execute right 200 == (some [false, false, false, true, false], 73),
   execute left 38 == execute left 200,
   execute right 73 == execute right 200,
   (execute left 37).1.isNone, (execute right 72).1.isNone,
   lookupSteps first left == 38, lookupSteps first right == 73,
   lookupBudget 1 1 2 == 108].all id

end Native
end CryptoOracle.RandomOracle.PolygraphExamples
