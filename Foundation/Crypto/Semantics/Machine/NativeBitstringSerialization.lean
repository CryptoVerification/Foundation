import Foundation.Crypto.Semantics.Machine.NativeSerializationConstraint
import Foundation.Crypto.Semantics.Machine.NativeDelimitedWriterResources

/-! A positive serialization witness on a layout-restricted domain.
The source bitstring is physically present and the output capacity is
explicit. The emitted packet determines the entire canonical source layout,
so faithful serialization is compatible with native cell observations. -/
namespace Machine.NativeBitstringSerialization
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def input (data : List Bool) : NativeDelimitedWriter.Input := {data := data}

def entry (data : List Bool) : Configuration := NativeDelimitedWriter.initial (input data)

def domain (source : Configuration) : Prop := ∃ data, source = entry data

def encode (source : Configuration) : List Bool := FiniteBitEncoding.delimit source.inputTape.bits

theorem entry_data (data : List Bool) : (entry data).inputTape.bits = data := by
  cases data <;>
    simp [entry, NativeDelimitedWriter.initial_eq, input, OneTimePad.delimitedTape, Tape.bits]

theorem finish_bits (data : List Bool) :
    (NativeDelimitedWriter.finish (input data)).outputBits = FiniteBitEncoding.delimit data := by
  simp [Configuration.outputBits, NativeDelimitedWriter.finish_output, input, Tape.bits]

/-- This serializer executes the actual fixed 15-instruction writer. -/
noncomputable def serializer : NativeSerializer domain encode where
  code := NativeFlaggedRequest.code
  budget := fun source => 8 * source.inputTape.bits.length + 4
  complete := by
    intro source hSource state hState
    obtain ⟨data, rfl⟩ := hSource
    rw [entry_data] at hState
    change state ∈ (evalConfigWithin NativeFlaggedRequest.code
      (NativeDelimitedWriter.initial (input data)) (8 * data.length + 4)).support at hState
    have hRun := NativeDelimitedWriter.run (input data)
    change evalConfigWithin NativeFlaggedRequest.code (NativeDelimitedWriter.initial (input data))
      (8 * data.length + 4) = PMF.pure (NativeDelimitedWriter.finish (input data)) at hRun
    rw [hRun, PMF.mem_support_pure_iff] at hState
    subst state
    rfl
  realizes := by
    intro source hSource
    obtain ⟨data, rfl⟩ := hSource
    rw [entry_data]
    change (evalConfigWithin NativeFlaggedRequest.code
      (NativeDelimitedWriter.initial (input data)) (8 * data.length + 4)).map Configuration.outputBits = _
    have hRun := NativeDelimitedWriter.run (input data)
    change evalConfigWithin NativeFlaggedRequest.code (NativeDelimitedWriter.initial (input data))
      (8 * data.length + 4) = PMF.pure (NativeDelimitedWriter.finish (input data)) at hRun
    rw [hRun, PMF.pure_map]
    change PMF.pure ((NativeDelimitedWriter.finish (input data)).outputBits) = _
    rw [finish_bits]
    simp [encode, entry_data]

/-- The emitted bits recover the whole source on this restricted domain. -/
theorem encode_injective_on_domain (first second : Configuration) (hFirst : domain first) (hSecond : domain second)
    (same : encode first = encode second) : first = second := by
  obtain ⟨firstData, rfl⟩ := hFirst
  obtain ⟨secondData, rfl⟩ := hSecond
  unfold encode at same
  rw [entry_data, entry_data] at same
  have h := congrArg (fun raw => FiniteBitEncoding.undelimit (raw ++ [])) same
  simp only [FiniteBitEncoding.undelimit_delimit, Option.some.injEq, Prod.mk.injEq, and_true] at h
  exact congrArg entry h

theorem entry_cells (data : List Bool) : (entry data).tapeCells = 3 * data.length + 3 := by
  simpa [entry, input] using NativeDelimitedWriter.initial_cells (input data)

theorem budget (data : List Bool) : serializer.budget (entry data) = 8 * data.length + 4 := by
  change 8 * (entry data).inputTape.bits.length + 4 = _
  rw [entry_data]

end Machine.NativeBitstringSerialization
