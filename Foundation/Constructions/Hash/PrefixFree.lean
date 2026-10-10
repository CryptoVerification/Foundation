import Foundation.Crypto.Semantics.Oracle.Program
import Foundation.Constructions.Symmetric.OneTimePad

/-! Prefix-free block encoding and Merkle–Damgård iteration expressed in
Foundation's adaptive oracle syntax. A data block has marker `false`; the
unique terminal block has marker `true` and a fixed payload. This is a
terminator-block variant of the marker encoding, not length strengthening.
There is no fixed-width message-length field. -/
namespace Foundation.Hash

open CryptoOracle
open Foundation.Symmetric

variable {Payload Digest : Type}

def encode (terminal : Payload) (message : List Payload) : List (Bool × Payload) :=
  message.map (fun block => (false, block)) ++ [(true, terminal)]

@[simp] theorem encode_length (terminal : Payload) (message : List Payload) :
    (encode terminal message).length = message.length + 1 := by
  simp [encode]

/-- A complete encoding cannot be a strict prefix of another encoding. -/
theorem encode_prefix (terminal : Payload) (left right : List Payload)
    (h : encode terminal left <+: encode terminal right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons block rest =>
          obtain ⟨suffix, hs⟩ := h
          simp [encode] at hs
  | cons block rest ih =>
      cases right with
      | nil =>
          have hl := h.length_le
          simp only [encode_length, List.length_cons, List.length_nil] at hl
          omega
      | cons other tail =>
          obtain ⟨suffix, hs⟩ := h
          simp only [encode, List.map_cons, List.cons_append, List.cons.injEq,
            Prod.mk.injEq, true_and] at hs
          exact congrArg₂ List.cons hs.1 (ih tail ⟨suffix, hs.2⟩)

theorem encode_injective (terminal : Payload) : Function.Injective (encode terminal) := by
  intro left right he
  apply encode_prefix terminal left right
  exact ⟨[], by simpa using he⟩

/-- Each block becomes exactly one compression-oracle query. The chaining
value returned by that query determines the next query. -/
def iterate (initial : Digest) : List Payload → Program (Digest × Payload) Digest Digest
  | [] => .done initial
  | block :: rest => .query (initial, block) (fun digest => iterate digest rest)

theorem iterate_queries (initial : Digest) (blocks : List Payload) :
    (iterate initial blocks).BoundedQueries blocks.length := by
  induction blocks generalizing initial with
  | nil => exact .done initial 0
  | cons block rest ih => exact .query (initial, block) _ rest.length ih

def prefixFreeMD (initial : Digest) (terminal : Payload) (message : List Payload) :
    Program (Digest × (Bool × Payload)) Digest Digest :=
  iterate initial (encode terminal message)

theorem prefixFreeMD_queries (initial : Digest) (terminal : Payload) (message : List Payload) :
    (prefixFreeMD initial terminal message).BoundedQueries (message.length + 1) := by
  simpa only [prefixFreeMD, encode_length] using iterate_queries initial (encode terminal message)

/-- With κ-bit payloads, compression takes an n-bit chaining value and a
(κ+1)-bit marked block, and returns n bits. -/
abbrev BitHash (n κ : Nat) :=
  Program (Bits n × (Bool × Bits κ)) (Bits n) (Bits n)

end Foundation.Hash
