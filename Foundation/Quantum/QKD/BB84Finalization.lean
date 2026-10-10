import Foundation.Quantum.QKD.BB84Randomized
import Foundation.Quantum.QKD.IdealKey

/-! Actual finite-output hashing of the randomized BB84 raw joint state with
fresh public randomness. This connects the ideal-key comparison interface to
BB84; it does not assert a leftover-hash lemma, error correction, authentication,
or real-to-ideal security. The hashing family is a parameter, not a security
axiom. The existing arbitrary block attack is retained. -/
namespace Foundation.Quantum.QKD.Finalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
variable {n length : Nat} {S : Type}

abbrev RawKey (n : Nat) := Fin n → Option (Fin 2)
abbrev Transcript (n : Nat) (S : Type) := RawProtocol.PublicRecord n × S

/-- Publicly announce the hash seed and hash both private raw keys on
acceptance. On abort no key is emitted. Error correction is not inserted here. -/
def output (seed : S) (hash : S → RawKey n → IdealKey.Key length) (r : RawProtocol.Output n) :
    IdealKey.Output (Transcript n S) length where
  transcript := (r.transcript,seed)
  accepted := r.transcript.accepted
  aliceKey := if r.transcript.accepted then some (hash seed r.aliceKey) else none
  bobKey := if r.transcript.accepted then some (hash seed r.bobKey) else none

theorem output_abort (seed : S) (hash : S → RawKey n → IdealKey.Key length) (r : RawProtocol.Output n)
    (h : r.transcript.accepted = false) :
    (output seed hash r).aliceKey = none ∧ (output seed hash r).bobKey = none := by
  simp [output,h]

theorem output_agree (seed : S) (hash : S → RawKey n → IdealKey.Key length) (r : RawProtocol.Output n)
    (h : r.aliceKey = r.bobKey) :
    (output seed hash r).aliceKey = (output seed hash r).bobKey := by simp [output,h]

variable [Fintype S]

/-- A verified physical channel keeps Eve's quantum register when changing
 the classical output. It does not merely define a marginal PMF. -/
def channel (e : Space) (seed : S) (hash : S → RawKey n → IdealKey.Key length) :
    Channel (.tensor (.register (Fintype.card (RawProtocol.Output n))) e)
      (.tensor (IdealKey.register (Transcript n S) length) e) :=
  classicalMap e (fun r => Fintype.equivFin _ (output seed hash ((Fintype.equivFin _).symm r)))

/-- The actual hashed joint state: raw keys, public transcript and Eve came
 from the block protocol; the hash seed is sampled independently afterwards. -/
def state {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat)
    (p : PMF S) (hash : S → RawKey n → IdealKey.Key length) :
    Density (.tensor (IdealKey.register (Transcript n S) length) e) :=
  Density.mixture p (fun seed => (channel e seed hash).run (Randomized.keyState A k minKey tolerance))

/-- The public view of each hashed branch factors through the old public
 record and the new seed; private hash outputs are not announced. -/
theorem public_channel {e : Space} (ρ : Density (.tensor (.register (Fintype.card (RawProtocol.Output n))) e))
    (seed : S) (hash : S → RawKey n → IdealKey.Key length) :
    ((IdealKey.publicChannel e).run ((channel e seed hash).run ρ)).matrix =
      ((classicalMap e (fun r => Fintype.equivFin ((Transcript n S) × Bool)
        (let o : RawProtocol.Output n := (Fintype.equivFin _).symm r
         ((o.transcript,seed),o.transcript.accepted)))).run ρ).matrix := by
  change (classicalMap e IdealKey.publicLabel).toKraus.apply
    ((classicalMap e (fun r => Fintype.equivFin _ (output seed hash ((Fintype.equivFin _).symm r)))).toKraus.apply ρ.matrix) = _
  rw [classicalMap_compose]
  have heq : IdealKey.publicLabel ∘ (fun r => Fintype.equivFin _
      (output seed hash ((Fintype.equivFin (RawProtocol.Output n)).symm r))) =
      (fun r => Fintype.equivFin ((Transcript n S) × Bool)
        (let o : RawProtocol.Output n := (Fintype.equivFin _).symm r
         ((o.transcript,seed),o.transcript.accepted))) := by
    funext r
    simp only [Function.comp_apply, IdealKey.publicLabel, Equiv.symm_apply_apply, IdealKey.publicView, output]
  rw [heq]
  rfl

/-- Idealization keeps the full public transcript, abort flag and Eve of
 this actual protocol output. This equality supplies no secrecy bound. -/
theorem ideal_public {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat)
    (p : PMF S) (hash : S → RawKey n → IdealKey.Key length) :
    ((IdealKey.publicChannel e).run (IdealKey.idealize (state A k minKey tolerance p hash))).matrix =
      ((IdealKey.publicChannel e).run (state A k minKey tolerance p hash)).matrix :=
  IdealKey.public_idealize _

/-- A security bound for the actual protocol implies its final-key
 disagreement bound. The security premise remains a separate obligation. -/
theorem security_correctness {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat)
    (p : PMF S) (hash : S → RawKey n → IdealKey.Key length) (ε : ℝ)
    (h : IdealKey.Secure (state A k minKey tolerance p hash) ε) :
    (recordEvent e (fun r => let o : IdealKey.Output (Transcript n S) length := (Fintype.equivFin _).symm r
      o.aliceKey ≠ o.bobKey)).probability (state A k minKey tolerance p hash) ≤ ε :=
  IdealKey.secure_correctness h

end
end Foundation.Quantum.QKD.Finalization
