import Foundation.Crypto.Semantics.Machine.ChooseRangeValidation
import Foundation.Crypto.Semantics.Machine.BitstringRewind

namespace Machine.ChooseRangeInputRewind

private def rewindEntry : Nat := ChooseRangeValidation.program.length + 1
private def finalPc : Nat := rewindEntry + rewindBitstring.length + 1
private def first : Program := ChooseRangeValidation.program.asSubroutine 0 rewindEntry

/-- After the range gate has restored both delimiters, physically rewind
the original framed request. The range status remains on the output tape;
there is no request reconstruction or uncharged tape reset. -/
def program : Program := Program.withSubroutine first rewindBitstring [.halt] finalPc

private theorem first_layout : program =
    Program.withSubroutine [] ChooseRangeValidation.program
      (rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt]) rewindEntry := by
  simp [program, first, Program.withSubroutine, rewindEntry, Program.asSubroutine_length]

private theorem final_step (c : Configuration) (hPc : c.pc = finalPc)
    (hActive : c.halted = false) : Step program c { c with halted := true } := by
  have hLookup : program[finalPc]? = some .halt := by
    have hIndex : finalPc = first.length + rewindBitstring.length + 1 + 0 := by
      simp [finalPc, first, rewindEntry, Program.asSubroutine_length]
    unfold program
    rw [hIndex, Program.withSubroutine_getElem?_suffix]
    rfl
  simp [Step, successors, next, hPc, hActive, hLookup, Instruction.next]

/-- Both numerical comparisons may accept or reject. In either case the
same original framed request, including every state bit, is restored under
the input head, while the conjunction remains available on the other tape. -/
theorem runs_matching (n width : Nat)
    (modulus suffix firstBits secondBits tail : List Bool)
    (hModulus : modulus.length = width)
    (hInstance : (modulus ++ suffix).length = 3*width)
    (hFirst : firstBits.length = width) (hSecond : secondBits.length = width) :
    let reply := false :: FiniteBitEncoding.delimit firstBits ++
      FiniteBitEncoding.delimit secondBits ++ tail
    let raw := encodeSecurityParameter n ++ frame (modulus ++ suffix) ++ frame reply
    ∃ target used,
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits raw) ∧
      target.outputTape.left.getD 0 none = some (decide
        (Binary.value firstBits < Binary.value modulus ∧
          Binary.value secondBits < Binary.value modulus)) := by
  dsimp only
  let instanceBits := modulus ++ suffix
  let reply := false :: FiniteBitEncoding.delimit firstBits ++
    FiniteBitEncoding.delimit secondBits ++ tail
  let raw := encodeSecurityParameter n ++ frame instanceBits ++ frame reply
  let before := some false :: List.replicate reply.length (some true) ++
    instanceBits.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true)
  let prefixBits := encodeSecurityParameter n ++
    frame instanceBits ++ encodeSecurityParameter reply.length ++
      (false :: FiniteBitEncoding.delimit firstBits ++ DelimitedTapeComparison.marked secondBits)
  obtain ⟨checked, u₁, run₁, hHalt₁, hStatus₁, hInput₁, _⟩ :=
    ChooseRangeValidation.runs_matching_layout n width modulus suffix firstBits secondBits tail
      hModulus hInstance hFirst hSecond
  obtain ⟨v₁, _, embedded₁⟩ := run₁.withSubroutine_halted
    [] ChooseRangeValidation.program (rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt])
    rewindEntry (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (checked.resumeAt rewindEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  have hSaved : prefixBits.reverse.map some =
      (DelimitedTapeComparison.marked secondBits).reverse.map some ++
        some false :: ((DelimitedTapeComparison.marked firstBits).reverse.map some ++ some false :: before) := by
    simp [prefixBits, before, encodeSecurityParameter, frame, DelimitedTapeComparison.delimit_eq_marked,
      List.reverse_append, List.reverse_cons,
      List.map_append, List.append_assoc, reply]
  have hRaw : prefixBits ++ false :: tail = raw := by
    simp [prefixBits, raw, reply, frame, encodeSecurityParameter, DelimitedTapeComparison.delimit_eq_marked,
      List.append_assoc]
  let canonical : Configuration :=
    { inputTape := { left := prefixBits.reverse.map some, current := some false, right := tail.map some },
      outputTape := checked.outputTape }
  have r₂ := rewindBitstring_runs_from prefixBits (some false) (tail.map some) checked.outputTape
  obtain ⟨v₂, _, embedded₂⟩ := r₂.withSubroutine_halted first rewindBitstring [.halt] finalPc
    (Nat.zero_le _) rfl rfl
  have hCall : (canonical.rebasePc first.length).Equivalent (checked.resumeAt rewindEntry) := by
    refine ⟨?_, rfl, ?_, Tape.Equivalent.refl _⟩
    · simp [canonical, first, rewindEntry, Configuration.rebasePc, Configuration.resumeAt,
        Program.asSubroutine_length]
    · change ({ left := prefixBits.reverse.map some, current := some false,
                  right := tail.map some } : Tape).Equivalent checked.inputTape
      rw [hSaved]
      exact hInput₁.symm
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({ right := prefixBits.map some ++ some false :: tail.map some } : Tape).moveRight,
      outputTape := checked.outputTape, halted := true }
  have r₂' : RunsFor program (canonical.rebasePc first.length) (rewound.resumeAt finalPc) v₂ := embedded₂
  obtain ⟨actual, actualRun₂, hActual⟩ := r₂'.exists_equivalent hCall
  have hPc : actual.pc = finalPc := by simpa [Configuration.resumeAt] using hActual.1.symm
  have hActive : actual.halted = false := hActual.2.1.symm
  refine ⟨{ actual with halted := true }, v₁+v₂+1,
    (r₁.trans actualRun₂).succ (final_step _ hPc hActive), rfl, ?_, ?_⟩
  · have hLayout : rewound.inputTape.Equivalent (Tape.ofBits raw) := by
      have hCells : prefixBits.map some ++ some false :: tail.map some = raw.map some := by
        rw [← hRaw]
        simp only [List.map_append, List.map_cons]
      change ({ right := prefixBits.map some ++ some false :: tail.map some } : Tape).moveRight.Equivalent _
      rw [hCells]
      cases raw with
      | nil => exact ⟨rfl, by intro i; cases i <;> rfl, fun _ => rfl⟩
      | cons bit rest => exact ⟨rfl, by intro i; cases i <;> rfl, fun _ => rfl⟩
    exact hActual.2.2.1.symm.trans hLayout
  · exact (hActual.2.2.2.2.1 0).symm.trans hStatus₁

def budget (length : Nat) : Nat := 3*ChooseRangeValidation.budget length + 3*length + 20

/-- Arbitrary malformed finite requests also halt. The rewind bound is
charged to the actual storage left by the range checks. -/
theorem runs_any (raw : List Bool) :
    ∃ target used, used ≤ budget raw.length ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true := by
  obtain ⟨checked, u₁, hu₁, run₁, hHalt₁⟩ := ChooseRangeValidation.runs_any raw
  obtain ⟨v₁, hv₁, embedded₁⟩ := run₁.withSubroutine_halted
    [] ChooseRangeValidation.program (rewindBitstring.asSubroutine rewindEntry finalPc ++ [.halt])
    rewindEntry (Nat.zero_le _) rfl hHalt₁
  have r₁ : RunsFor program (Configuration.initial raw) (checked.resumeAt rewindEntry) v₁ := by
    rw [first_layout]
    simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add] using embedded₁
  obtain ⟨rewound, u₂, hu₂, run₂, hHalt₂, _⟩ :=
    rewindBitstring_terminates_from checked.inputTape checked.outputTape
  obtain ⟨v₂, hv₂, embedded₂⟩ := run₂.withSubroutine_halted first rewindBitstring [.halt] finalPc
    (Nat.zero_le _) rfl hHalt₂
  have r₂ : RunsFor program (checked.resumeAt rewindEntry) (rewound.resumeAt finalPc) v₂ := by
    simpa [program, first, rewindEntry, Program.asSubroutine_length,
      Configuration.resumeAt, Configuration.rebasePc] using embedded₂
  refine ⟨{ rewound.resumeAt finalPc with halted := true }, v₁+v₂+1, ?_,
    (r₁.trans r₂).succ (final_step _ rfl rfl), rfl⟩
  have hs := GuardedCompiler.sourceStorage_le_of_run run₁
  have hInitial : GuardedCompiler.sourceStorage (Configuration.initial raw) ≤ raw.length+2 := by
    cases raw <;> simp [GuardedCompiler.sourceStorage, Configuration.initial, Tape.ofBits, Tape.cells] <;> omega
  have hLeft : checked.inputTape.left.length ≤ checked.inputTape.cells := by
    simp only [Tape.cells]; omega
  simp only [GuardedCompiler.sourceStorage] at hs hInitial
  dsimp only [budget]
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> native_decide

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (budget raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt⟩ := runs_any raw
  have hHalts : HaltsWith program raw target.outputBits used := ⟨target, run, hHalt, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit no_randomBit).mono hUsed

theorem budget_polynomial : PolynomiallyBounded budget := by
  unfold budget
  exact (((PolynomiallyBounded.const 3).mul ChooseRangeValidation.budget_polynomial).add
    ((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id)).add (PolynomiallyBounded.const 20)

theorem polynomialTime : PolynomialTime program := ⟨budget, budget_polynomial, haltsWithin⟩

end Machine.ChooseRangeInputRewind
