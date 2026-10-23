import Foundation.Logic.Polygraph.FourAssociation

/-! Run the existing proof-pasting elaborators in the current goal's local
context, including locally named paths. The output remains an ordinary
kernel-checked Four term. -/
namespace Foundation.Logic.Polygraph.FourAssociationContext
open Lean Elab Tactic
elab "four_assoc_ctx" : tactic => withMainContext do
  evalTactic (← `(tactic| four_assoc))
elab "four_rewrite_ctx " witness:term : tactic => withMainContext do
  evalTactic (← `(tactic| four_rewrite $witness))
end Foundation.Logic.Polygraph.FourAssociationContext
