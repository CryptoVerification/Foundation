import Foundation.Constructions.Symmetric.EncryptThenMAC.PhysicalGeneratorImplementation
import Foundation.Crypto.Semantics.Machine.PrivateBitGenerationRanking
import Foundation.Crypto.Semantics.Machine.TypedNativeComposition
import Foundation.Crypto.Semantics.Machine.NativeComponent
import Foundation.Crypto.Semantics.Machine.ControlClosure

/-! Assemble a uniform native seed sampler and a native expander into one
fixed finite generator program. The expander receives the actual returned
seed tape, including its head position, and may retain arbitrary private
scratch state. Only its supported exported tape must implement G.generate.
This is an implementation theorem, not a pseudorandomness assumption. -/
namespace Foundation.Symmetric.EncryptThenMAC.SeededGeneratorImplementation
open Machine Foundation.Probability Foundation.Symmetric TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

/-- The fixed sampler never leaves its code while still active. -/
theorem sampler_closed (start target : Configuration) (hp : start.pc < OneTimePad.keygen.length)
    (hs : Step OneTimePad.keygen start target) (ha : target.halted = false) :
    target.pc < OneTimePad.keygen.length := by
  exact Program.controlClosed_step (code := OneTimePad.keygen) (by decide) start target hp hs ha

noncomputable abbrev sampler (G : Generator) (n : Nat) := PrivateBitGeneration.Ranked.typed (G.seedLength n)

noncomputable def samplerComponent (G : Generator) (n : Nat) : NativeComponent Unit (Bits (G.seedLength n)) where
  procedure := sampler G n
  closed := sampler_closed
  entry := fun _ => by change 0 < 6; decide
  active := fun _ => rfl
  halted := fun _ _ _ => rfl

/-- The seed stage now uses independently ranked stopping and records its
actual native first-arrival time, rather than a declared padded duration. -/
theorem sampler_costed (G : Generator) (n : Nat) :
    ((sampler G n).execution.costed ()).map (fun result =>
      ((sampler G n).execution.exit () result.1, result.2)) =
      runToBoundary (stepPMF OneTimePad.keygen) Configuration.halted (5 * G.seedLength n + 2)
        (Configuration.initial (List.replicate (G.seedLength n) true)) :=
  PrivateBitGeneration.Ranked.typed_costed (G.seedLength n)

noncomputable def seedEntry (G : Generator) (n : Nat) (seed : Bits (G.seedLength n)) : Configuration :=
  ((sampler G n).execution.exit () seed).resumeAt ((sampler G n).code.length + 1)

/-- Decode a public key from a full physical result. This is an observation
of the existing output tape, not an operational preparation step. -/
def key (G : Generator) (n : Nat) (machine : Configuration) : Bits (G.outputLength n) :=
  PrivateBitGeneration.read (G.outputLength n) () machine

theorem key_of_tape (G : Generator) (n : Nat) (machine : Configuration) (bits : Bits (G.outputLength n))
    (h : machine.outputTape = ResponseExport.endTape bits.toList) : key G n machine = bits := by
  have ht : machine.outputBits = bits.toList := by
    rw [Configuration.outputBits, h]
    simp [ResponseExport.endTape, Tape.bits, List.filterMap_map, Function.comp_def]
  funext index
  simp [key, PrivateBitGeneration.read, ht, Bits.toList]

/-- A single finite expander code, with parameter-dependent contracts on
actual input configurations. Seed entries already contain the sampled tape;
no uncharged copying, resetting or evaluation of G.generate is performed. -/
structure ConfigurationExpander (G : Generator) where
  Output : Nat → Type u
  code : Machine.Program
  execution : ∀ n, TimedExecution.Procedure (stepPMF code) Configuration (Output n)
  closed : ∀ start target, start.pc < code.length → Step code start target →
    target.halted = false → target.pc < code.length
  entry : ∀ n machine, (execution n).entry machine = machine.resumeAt 0
  nonempty : 0 < code.length
  halted : ∀ n input output, output ∈ ((execution n).semantics input).support →
    ((execution n).exit input output).halted = true
  cap : Nat → Nat
  bounded : ∀ n seed, (execution n).budget (seedEntry G n seed) ≤ cap n
  tape : ∀ n seed output, output ∈ ((execution n).semantics (seedEntry G n seed)).support →
    ((execution n).exit (seedEntry G n seed) output).outputTape =
      ResponseExport.endTape (G.generate n seed).toList


/-- Only actual seed inputs require an execution contract. Malformed or
unrelated machine configurations are outside this component precondition. -/
structure Expander (G : Generator) where
  Output : Nat → Type u
  code : Machine.Program
  execution : ∀ n, TimedExecution.Procedure (stepPMF code) (Bits (G.seedLength n)) (Output n)
  closed : ∀ start target, start.pc < code.length → Step code start target →
    target.halted = false → target.pc < code.length
  entry : ∀ n seed, (execution n).entry seed = (seedEntry G n seed).resumeAt 0
  nonempty : 0 < code.length
  halted : ∀ n input output, output ∈ ((execution n).semantics input).support →
    ((execution n).exit input output).halted = true
  cap : Nat → Nat
  bounded : ∀ n seed, (execution n).budget seed ≤ cap n
  tape : ∀ n seed output, output ∈ ((execution n).semantics seed).support →
    ((execution n).exit seed output).outputTape =
      ResponseExport.endTape (G.generate n seed).toList

namespace ConfigurationExpander
/-- Existing contracts on every configuration restrict to the actual seeds. -/
noncomputable def typed {G : Generator} (E : ConfigurationExpander.{u} G) : Expander G where
  Output := E.Output
  code := E.code
  execution := fun n => (E.execution n).reindex (seedEntry G n)
  closed := E.closed
  entry := fun n seed => E.entry n (seedEntry G n seed)
  nonempty := E.nonempty
  halted := fun n seed => E.halted n (seedEntry G n seed)
  cap := E.cap
  bounded := E.bounded
  tape := E.tape

theorem typed_code {G : Generator} (E : ConfigurationExpander.{u} G) : E.typed.code = E.code := rfl

theorem typed_entry {G : Generator} (E : ConfigurationExpander.{u} G) (n : Nat) (seed : Bits (G.seedLength n)) :
    (E.typed.execution n).entry seed = (E.execution n).entry (seedEntry G n seed) := rfl

theorem typed_budget {G : Generator} (E : ConfigurationExpander.{u} G) (n : Nat) (seed : Bits (G.seedLength n)) :
    (E.typed.execution n).budget seed = (E.execution n).budget (seedEntry G n seed) := rfl

/-- Restriction preserves the entire original result/time distribution. -/
theorem typed_costed {G : Generator} (E : ConfigurationExpander.{u} G) (n : Nat) (seed : Bits (G.seedLength n)) :
    (E.typed.execution n).costed seed = (E.execution n).costed (seedEntry G n seed) := rfl

end ConfigurationExpander

namespace Expander
variable {G : Generator} (E : Expander.{u} G)

def native (n : Nat) : Machine.Procedure (Bits (G.seedLength n)) (E.Output n) := ⟨E.code, E.execution n⟩

def component (n : Nat) : NativeComponent (Bits (G.seedLength n)) (E.Output n) where
  procedure := E.native n
  closed := E.closed
  entry := fun seed => by dsimp only [native]; rw [E.entry]; exact E.nonempty
  active := fun seed => by dsimp only [native]; rw [E.entry]; rfl
  halted := E.halted n

/-- Logical seed labels describe an existing tape, not free preparation. -/
noncomputable def link (n : Nat) : TypedNativeComposition.Link (sampler G n) (E.native n) :=
  (samplerComponent G n).link (E.component n) (PrivateBitGeneration.read (G.seedLength n))
    (fun input seed _ => PrivateBitGeneration.read_exit (G.seedLength n) input seed)
    (fun _ seed => seed)
    (by
      intro input seed _
      cases input
      change ((E.execution n).entry seed).rebasePc _ = _
      rw [E.entry]
      simp only [seedEntry, Configuration.resumeAt, Configuration.rebasePc,
        Configuration.mk.injEq, and_true, true_and, Nat.add_zero]
      exact ⟨rfl, rfl⟩)
    (fun _ => E.cap n) (fun _ seed _ => E.bounded n seed)

noncomputable def assembled (n : Nat) : Machine.Procedure Unit Configuration := (E.link n).native

noncomputable def assembledComponent (n : Nat) : NativeComponent Unit Configuration := (E.link n).component

theorem assembled_operational (n : Nat) :
    TimedExecution.Procedure.Operational (E.assembled n).execution := (E.link n).operational

theorem assembled_code (n : Nat) : (E.assembled n).code = OneTimePad.keygen.followedBy E.code := rfl

theorem assembled_budget (n : Nat) :
    (E.assembled n).execution.budget () = 5 * G.seedLength n + E.cap n + 3 := by
  rw [assembled, TypedNativeComposition.Link.budget]
  change (PrivateBitGeneration.Ranked.typed (G.seedLength n)).execution.budget () + E.cap n + 1 = _
  rw [PrivateBitGeneration.Ranked.typed_budget]
  omega

theorem assembled_semantics (n : Nat) :
    (E.assembled n).execution.semantics () =
      (uniform (Bits (G.seedLength n))).bind (fun seed =>
        ((E.execution n).semantics seed).map (fun output =>
          {((E.execution n).exit seed output).resumeAt
            (OneTimePad.keygen.length + E.code.length + 2) with halted := true})) := by
  rw [assembled, TypedNativeComposition.Link.semantics]
  rw [show (sampler G n).execution.semantics () = uniform (Bits (G.seedLength n)) from
    PrivateBitGeneration.Ranked.typed_semantics (G.seedLength n)]
  rfl

include E in
theorem exports (n : Nat) (input : Unit) (machine : Configuration)
    (h : machine ∈ ((E.assembled n).execution.semantics input).support) :
    ExportedProcedure.Valid (key G n) Bits.toList machine := by
  cases input
  rw [assembled_semantics, PMF.mem_support_bind_iff] at h
  obtain ⟨seed, _, h⟩ := h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨output, ho, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  have ht := E.tape n seed output ho
  have hk := key_of_tape G n
    {((E.execution n).exit seed output).resumeAt
      (OneTimePad.keygen.length + E.code.length + 2) with halted := true}
    (G.generate n seed) ht
  change ((E.execution n).exit seed output).outputTape = _
  rw [hk]
  exact ht

/-- Run the actual linked code from the sampler's physical marker input. -/
theorem assembled_run (n horizon : Nat)
    (hTime : 5 * G.seedLength n + E.cap n + 3 ≤ horizon) :
    evalConfigWithin (OneTimePad.keygen.followedBy E.code)
      (Configuration.initial (List.replicate (G.seedLength n) true)) horizon =
      (E.assembled n).execution.semantics () := by
  have h := (E.assembled n).final_run ()
    (fun machine hm => (E.exports n () machine hm).1) horizon
    (by rw [assembled_budget]; exact hTime)
  change evalConfigWithin (OneTimePad.keygen.followedBy E.code)
    ((Configuration.initial (List.replicate (G.seedLength n) true)).rebasePc 0) horizon =
      ((E.assembled n).execution.semantics ()).map id at h
  rw [PMF.map_id] at h
  simpa only [Configuration.rebasePc, Configuration.initial, Nat.zero_add] using h

include E in
theorem implements (n : Nat) (input : Unit) :
    ((E.assembled n).execution.semantics input).map (key G n) = G.real n := by
  cases input
  rw [assembled_semantics, PMF.map_bind, Generator.real, PMF.map]
  congr 1
  funext seed
  rw [PMF.map_comp, PMF.map, ← PMF.bindOnSupport_eq_bind]
  trans ((E.execution n).semantics seed).bindOnSupport
    (fun _ _ => PMF.pure (G.generate n seed))
  · congr 1
    funext output ho
    exact congrArg PMF.pure (key_of_tape G n _ _ (E.tape n seed output ho))
  · rw [PMF.bindOnSupport_eq_bind]
    exact PMF.bind_const _ _

/-- A real finite generator implementation obtained from the native sampler
and expander contracts. The output retains the entire physical final state. -/
noncomputable def physical : ProjectedGeneratedBlockMask.PRG.PhysicalImplementation G where
  Input := fun _ => Unit
  Output := fun _ => Configuration
  code := OneTimePad.keygen.followedBy E.code
  execution := fun n => (E.assembled n).execution
  key := key G
  exports := E.exports
  implements := E.implements

noncomputable def projected : ProjectedGeneratedBlockMask.PRG.Implementation G := E.physical.projected

theorem projected_code : E.projected.code = OneTimePad.keygen.followedBy E.code := rfl

theorem projected_budget (n : Nat) :
    (E.projected.execution n).budget () = 5 * G.seedLength n + E.cap n + 3 := E.assembled_budget n

theorem time_polynomial (hSeed : PolynomiallyBounded G.seedLength) (hExpand : PolynomiallyBounded E.cap) :
    PolynomiallyBounded (fun n => (E.projected.execution n).budget ()) := by
  have h := (((PolynomiallyBounded.const 5).mul hSeed).add hExpand).add (PolynomiallyBounded.const 3)
  simpa only [projected_budget] using h

end Expander
end Foundation.Symmetric.EncryptThenMAC.SeededGeneratorImplementation
