import Foundation.Crypto.Semantics.Oracle.RequestExport

/-! Uniqueness of a terminated physical request layout. Proof-level layout
selection cannot change the parsed request or the preserved tape suffix. -/
namespace CryptoOracle.Interactive.RequestExport
set_option backward.isDefEq.respectTransparency false

private theorem terminated_injective (first second : List Bool) (firstTail secondTail : List (Option Bool))
    (h : first.map some ++ none :: firstTail = second.map some ++ none :: secondTail) :
    first = second ∧ firstTail = secondTail := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons bit first ih =>
      cases second with
      | nil => simp at h
      | cons other second =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq, Option.some.injEq] at h
          obtain ⟨he, ht⟩ := h
          obtain ⟨hb, hs⟩ := ih second ht
          exact ⟨by rw [he, hb], hs⟩

/-- The physical head and remaining cells determine both request and suffix.
Contents after the first delimiter remain part of the original tape. -/
theorem packetTape_injective {first second : List Bool} {firstTail secondTail before : List (Option Bool)}
    (h : packetTape before firstTail first = packetTape before secondTail second) :
    first = second ∧ firstTail = secondTail := by
  have hCells := congrArg (fun tape : Machine.Tape => tape.current :: tape.right) h
  have hFirst : (packetTape before firstTail first).current :: (packetTape before firstTail first).right =
      first.map some ++ none :: firstTail := by cases first <;> simp [packetTape]
  have hSecond : (packetTape before secondTail second).current :: (packetTape before secondTail second).right =
      second.map some ++ none :: secondTail := by cases second <;> simp [packetTape]
  rw [hFirst, hSecond] at hCells
  exact terminated_injective first second firstTail secondTail hCells

theorem packetTape_cells (before after : List (Option Bool)) (request : List Bool) :
    (packetTape before after request).cells = before.length + request.length + after.length + 1 := by
  cases request <;> simp [packetTape, Machine.Tape.cells] <;> omega

end CryptoOracle.Interactive.RequestExport
