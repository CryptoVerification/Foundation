import Mathlib.Data.List.Basic

/-! Agreement between private records and successful public records.
Runtime traces are newest-first; both observations preserve chronological
order. A failed public response creates no private signing record. -/
namespace Foundation.History
universe u v w
variable {Signed : Type u} {Public : Type v} {Value : Type w}

def Agreement (decode : Signed → Value) (observe : Public → Option Value)
    (signed : List Signed) (published : List Public) : Prop :=
  signed.reverse.map decode = published.reverse.filterMap observe

theorem empty (decode : Signed → Value) (observe : Public → Option Value) :
    Agreement decode observe [] [] := rfl

theorem failure (decode : Signed → Value) (observe : Public → Option Value)
    (signed : List Signed) (published : List Public) (response : Public)
    (h : Agreement decode observe signed published) (hFailure : observe response = none) :
    Agreement decode observe signed (response :: published) := by
  simpa [Agreement, List.reverse_cons, List.filterMap_append, hFailure] using h

theorem success (decode : Signed → Value) (observe : Public → Option Value)
    (signed : List Signed) (published : List Public) (record : Signed) (response : Public)
    (h : Agreement decode observe signed published) (hSuccess : observe response = some (decode record)) :
    Agreement decode observe (record :: signed) (response :: published) := by
  simpa [Agreement, List.reverse_cons, List.map_append, List.filterMap_append, hSuccess] using
    congrArg (fun history => history ++ [decode record]) h

end Foundation.History
