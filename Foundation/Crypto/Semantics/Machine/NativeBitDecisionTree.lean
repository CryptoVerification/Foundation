import Foundation.Crypto.Semantics.Machine.NativeBitChoice

/-! Compile a finite bit-indexed family of native leaves to one native program.
Reading consumes physical cells and retains the input history and both suffixes.
The host function is used to construct a finite instruction list, never as an
instruction executed by the machine. -/
namespace Machine.NativeBitDecisionTree
open Foundation.Probability

def compile : (n : ℕ) → ((Fin n → Bool) → Program) → Program
  | 0, leaves => leaves (fun i => Fin.elim0 i)
  | n + 1, leaves => NativeBitChoice.code
      (compile n (fun bits => leaves (Fin.cons false bits)))
      (compile n (fun bits => leaves (Fin.cons true bits)))

def preload : List Bool → Tape → Tape
  | [], suffix => suffix
  | bit :: bits, suffix =>
    {left := suffix.left, current := some bit,
      right := bits.map some ++ suffix.current :: suffix.right}

def afterRead (bits : List Bool) (suffix : Tape) : Tape :=
  {suffix with left := bits.reverse.map some ++ suffix.left}

theorem preload_moveRight_cons (bit : Bool) (bits : List Bool) (suffix : Tape) :
    (preload (bit :: bits) suffix).moveRight =
      preload bits {suffix with left := some bit :: suffix.left} := by
  cases bits <;> simp [preload, Tape.moveRight]

theorem afterRead_cons (bit : Bool) (bits : List Bool) (suffix : Tape) :
    afterRead bits {suffix with left := some bit :: suffix.left} =
      afterRead (bit :: bits) suffix := by
  simp [afterRead, List.map_append, List.append_assoc]

def Stops (p : Program) (input output : Tape) (steps : ℕ) : Prop :=
  ∀ finish, PaddedRunsFor p (NativeBitChoice.start input output) finish steps →
    finish.halted = true

theorem run_selected (zero one : Program) (input output : Tape) (bit : Bool)
    (hbit : input.current = some bit) (steps : ℕ)
    (halts : Stops (if bit then one else zero) input.moveRight output steps) :
    evalConfigWithin (NativeBitChoice.code zero one) (NativeBitChoice.start input output)
      (steps + 3) =
      (evalConfigWithin (if bit then one else zero)
        (NativeBitChoice.start input.moveRight output) steps).map
          (fun c => {c with pc := NativeBitChoice.returnPc zero one, halted := true}) := by
  cases bit with
  | false => exact NativeBitChoice.run_zero zero one input output hbit steps halts
  | true => exact NativeBitChoice.run_one zero one input output hbit steps halts

def finishControl : (n : ℕ) → ((Fin n → Bool) → Program) → Configuration → Configuration
  | 0, _, c => c
  | n + 1, leaves, c =>
      {c with pc := (NativeBitChoice.returnPc
        (compile n (fun bits => leaves (Fin.cons false bits)))
        (compile n (fun bits => leaves (Fin.cons true bits)))), halted := true}

theorem finishControl_overwrite (n : ℕ) (leaves : (Fin n → Bool) → Program)
    (c : Configuration) (pc : ℕ) :
    {finishControl n leaves c with pc := pc, halted := true} =
      {c with pc := pc, halted := true} := by
  cases n <;> rfl

theorem compile_contract (n : ℕ) :
    ∀ (leaves : (Fin n → Bool) → Program) (T : ℕ),
      (∀ bits input output, Stops (leaves bits) input output T) →
      ∀ (bits : Fin n → Bool) (suffix output : Tape),
        Stops (compile n leaves) (preload (List.ofFn bits) suffix) output (T + 3 * n) ∧
        evalConfigWithin (compile n leaves)
          (NativeBitChoice.start (preload (List.ofFn bits) suffix) output) (T + 3 * n) =
          (evalConfigWithin (leaves bits)
            (NativeBitChoice.start (afterRead (List.ofFn bits) suffix) output) T).map
              (finishControl n leaves) := by
  induction n with
  | zero =>
    intro leaves T hLeaves bits suffix output
    have hbits : (fun i : Fin 0 => Fin.elim0 i) = bits := by
      funext i
      exact Fin.elim0 i
    constructor
    · simpa [compile, hbits, preload] using hLeaves bits suffix output
    · change evalConfigWithin (leaves (fun i : Fin 0 => Fin.elim0 i))
        (NativeBitChoice.start suffix output) T =
        (evalConfigWithin (leaves bits) (NativeBitChoice.start suffix output) T).map id
      rw [hbits, PMF.map_id]
  | succ n ih =>
    intro leaves T hLeaves bits suffix output
    let zero := compile n (fun tail => leaves (Fin.cons false tail))
    let one := compile n (fun tail => leaves (Fin.cons true tail))
    let branchLeaves := fun tail => leaves (Fin.cons (bits 0) tail)
    let chosen := compile n branchLeaves
    let tailSuffix : Tape := {suffix with left := some (bits 0) :: suffix.left}
    have hTail := ih branchLeaves T
      (fun tail input output => hLeaves (Fin.cons (bits 0) tail) input output)
      (Fin.tail bits) tailSuffix output
    have hmove : (preload (List.ofFn bits) suffix).moveRight =
        preload (List.ofFn (Fin.tail bits)) tailSuffix := by
      rw [List.ofFn_succ, preload_moveRight_cons]
      rfl
    have hafter : afterRead (List.ofFn (Fin.tail bits)) tailSuffix =
        afterRead (List.ofFn bits) suffix := by
      rw [List.ofFn_succ]
      exact afterRead_cons (bits 0) (List.ofFn (Fin.tail bits)) suffix
    have hselect : (if bits 0 then one else zero) = chosen := by
      cases h : bits 0 <;> simp [zero, one, chosen, branchLeaves, h]
    have hChild : Stops chosen (preload (List.ofFn bits) suffix).moveRight output (T + 3 * n) := by
      rw [hmove]
      exact hTail.1
    have hSelected : Stops (if bits 0 then one else zero)
        (preload (List.ofFn bits) suffix).moveRight output (T + 3 * n) := by
      rw [hselect]
      exact hChild
    have hRun := run_selected zero one (preload (List.ofFn bits) suffix) output (bits 0)
      (by simp [List.ofFn_succ, preload]) (T + 3 * n) hSelected
    rw [hselect, hmove] at hRun
    have hFull : evalConfigWithin (compile (n + 1) leaves)
        (NativeBitChoice.start (preload (List.ofFn bits) suffix) output) (T + 3 * (n + 1)) =
        (evalConfigWithin chosen
          (NativeBitChoice.start (preload (List.ofFn (Fin.tail bits)) tailSuffix) output)
          (T + 3 * n)).map
            (fun c => {c with pc := NativeBitChoice.returnPc zero one, halted := true}) := by
      simpa only [compile, zero, one, Nat.mul_succ, Nat.add_assoc] using hRun
    constructor
    · intro finish run
      have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
      rw [hFull, PMF.mem_support_map_iff] at member
      obtain ⟨c, _, rfl⟩ := member
      rfl
    · have hLaw := hTail.2
      change evalConfigWithin chosen _ _ = _ at hLaw
      simp only [branchLeaves, Fin.cons_self_tail, hafter] at hLaw
      rw [hFull, hLaw, PMF.map_comp]
      congr 1
      funext c
      exact finishControl_overwrite n branchLeaves c (NativeBitChoice.returnPc zero one)

theorem compile_halts (n : ℕ) (leaves : (Fin n → Bool) → Program) (T : ℕ)
    (hLeaves : ∀ bits input output, Stops (leaves bits) input output T)
    (bits : Fin n → Bool) (suffix output : Tape) :
    Stops (compile n leaves) (preload (List.ofFn bits) suffix) output (T + 3 * n) :=
  (compile_contract n leaves T hLeaves bits suffix output).1

theorem compile_run (n : ℕ) (leaves : (Fin n → Bool) → Program) (T : ℕ)
    (hLeaves : ∀ bits input output, Stops (leaves bits) input output T)
    (bits : Fin n → Bool) (suffix output : Tape) :
    evalConfigWithin (compile n leaves)
      (NativeBitChoice.start (preload (List.ofFn bits) suffix) output) (T + 3 * n) =
      (evalConfigWithin (leaves bits)
        (NativeBitChoice.start (afterRead (List.ofFn bits) suffix) output) T).map
          (finishControl n leaves) :=
  (compile_contract n leaves T hLeaves bits suffix output).2

theorem compile_length_bound (n : ℕ) :
    ∀ (leaves : (Fin n → Bool) → Program) (L : ℕ),
      (∀ bits, (leaves bits).length ≤ L) →
      (compile n leaves).length + 6 ≤ (L + 6) * 2 ^ n := by
  induction n with
  | zero =>
    intro leaves L hLeaves
    simpa only [compile, pow_zero, Nat.mul_one] using
      Nat.add_le_add_right (hLeaves (fun i : Fin 0 => Fin.elim0 i)) 6
  | succ n ih =>
    intro leaves L hLeaves
    have hz := ih (fun bits => leaves (Fin.cons false bits)) L
      (fun bits => hLeaves (Fin.cons false bits))
    have ho := ih (fun bits => leaves (Fin.cons true bits)) L
      (fun bits => hLeaves (Fin.cons true bits))
    rw [compile, NativeBitChoice.code_length]
    calc
      _ = ((compile n (fun bits => leaves (Fin.cons false bits))).length + 6) +
          ((compile n (fun bits => leaves (Fin.cons true bits))).length + 6) := by omega
      _ ≤ (L + 6) * 2 ^ n + (L + 6) * 2 ^ n := Nat.add_le_add hz ho
      _ = (L + 6) * 2 ^ (n + 1) := by rw [pow_succ]; ring

end Machine.NativeBitDecisionTree
