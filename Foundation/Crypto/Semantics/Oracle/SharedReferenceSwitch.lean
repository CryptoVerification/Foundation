import Foundation.Crypto.Semantics.Oracle.SharedReference
import Foundation.Crypto.Semantics.Oracle.RepresentationSwitch
import Foundation.Logic.Polygraph.StructuralTransport

/-! Structural wiring of references BEFORE the original captured continuation
resumes. The actual prefix, one live recoded cache, actual policy choice and
complete final outcome are retained. Reference copying never forks the cache.
There is one serial continuation execution, not independent post-run copies. -/
namespace CryptoOracle.RandomOracle.Representation.SharedSwitch
open Foundation.Probability Foundation.Logic.Polygraph.StructuralTransport
variable {Input Response Result OldStored NewStored View Label : Type}
  [DecidableEq Input] [Fintype Response] [Nonempty Response]

noncomputable def joint (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Switch.Past Input Response Result OldStored → Label)
    (view : Switch.Past Input Response Result OldStored → View)
    (route : Switch.Past Input Response Result OldStored → View → Nat → SharedReference.Ref)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    PMF (View × Switch.Retained Input Response Result OldStored Label NewStored) :=
  ((Program.pauseAfter count program).run (oracle old) saved).bind fun past =>
    (SharedReference.run (route past (view past)) past.result (oracle (codecs (choose past)))
      (Switch.recode old (codecs (choose past)) past.state)).map fun last =>
        (view past, past, choose past, {last with trace := past.trace ++ last.trace})

theorem operational_joint (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Switch.Past Input Response Result OldStored → Label)
    (view : Switch.Past Input Response Result OldStored → View)
    (route : Switch.Past Input Response Result OldStored → View → Nat → SharedReference.Ref)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    joint old codecs choose view route count program saved =
      (Switch.joint old codecs choose count program saved).map (fun record => (view record.1, record)) := by
  simp only [joint, Switch.joint, SharedReference.run_eq, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem forget_view (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Switch.Past Input Response Result OldStored → Label)
    (view : Switch.Past Input Response Result OldStored → View)
    (route : Switch.Past Input Response Result OldStored → View → Nat → SharedReference.Ref)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    (joint old codecs choose view route count program saved).map Prod.snd =
      Switch.joint old codecs choose count program saved := by
  rw [operational_joint, PMF.map_comp]
  exact PMF.map_id _

theorem decoded_joint (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Switch.Past Input Response Result OldStored → Label)
    (view : Switch.Past Input Response Result OldStored → View)
    (route : Switch.Past Input Response Result OldStored → View → Nat → SharedReference.Ref)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    (joint old codecs choose view route count program saved).map (fun pair => (pair.1, Switch.decode old codecs pair.2)) =
      (Switch.reference old choose count program saved).map (fun record => (view record.1, record)) := by
  rw [operational_joint, PMF.map_comp]
  have law := congrArg (fun distribution => distribution.map (fun record => (view record.1, record)))
    (Switch.decoded_joint old codecs choose count program saved)
  simpa only [PMF.map_comp, Function.comp_def, Switch.decode] using law

theorem final_game (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Switch.Past Input Response Result OldStored → Label)
    (view : Switch.Past Input Response Result OldStored → View)
    (route : Switch.Past Input Response Result OldStored → View → Nat → SharedReference.Ref)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    (joint old codecs choose view route count program saved).map (fun pair => (Switch.decode old codecs pair.2).2.2) =
      program.run (oracle old) saved := by
  have law := congrArg (fun distribution => distribution.map (fun pair => pair.2.2.2))
    (decoded_joint old codecs choose view route count program saved)
  simpa only [PMF.map_comp, Function.comp_def, Switch.reference_final] using law

variable {Atom : Type} {first last : Shape Atom}

noncomputable def wired (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Switch.Past Input Response Result OldStored → Label)
    (wire : Wire first last)
    (inputs : Switch.Past Input Response Result OldStored → first.Value (fun _ => SharedReference.Ref))
    (route : Switch.Past Input Response Result OldStored → last.Value (fun _ => SharedReference.Ref) → Nat → SharedReference.Ref)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :=
  joint old codecs choose (fun past => wire.eval (fun _ => SharedReference.Ref) (inputs past)) route count program saved

theorem cell_joint {one two : Wire first last} (cell : Cell one two)
    (old : Input → Response ≃ OldStored) (codecs : Label → Input → Response ≃ NewStored)
    (choose : Switch.Past Input Response Result OldStored → Label)
    (inputs : Switch.Past Input Response Result OldStored → first.Value (fun _ => SharedReference.Ref))
    (route : Switch.Past Input Response Result OldStored → last.Value (fun _ => SharedReference.Ref) → Nat → SharedReference.Ref)
    (count : Nat) (program : Program Input Response Result) (saved : Table Input OldStored) :
    wired old codecs choose one inputs route count program saved = wired old codecs choose two inputs route count program saved := by
  unfold wired
  have same : (fun past => one.eval (fun _ => SharedReference.Ref) (inputs past)) =
      (fun past => two.eval (fun _ => SharedReference.Ref) (inputs past)) :=
    funext (fun past => cell.sound _ (inputs past))
  rw [same]

end CryptoOracle.RandomOracle.Representation.SharedSwitch
