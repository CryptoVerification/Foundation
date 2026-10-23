import Foundation.Crypto.Logic.Polygraph.MixedCircuitPresentedPathNaturality
import Foundation.Examples.MixedCircuitFusionHigher

/-! Exercise the path-valued interface on the real suffix-fusion macro.
The existing local definition cell is reused, not claimed new. This is macro
expansion with identity object maps, not yet wire-pass/fusion compatibility. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion.PathResidual
open Foundation.Logic.Polygraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def image {a b} {p q : Circuit signature a b} (change : Step rules p q) := embedTrack (expandStep change)

def embedding {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :=
  FourPathNaturality.replace id (fun change => Track.step change) path

def projection {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :=
  FourPathNaturality.replace id (fun change => image change) path

theorem embedding_eq {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    embedding path = path := by
  induction path <;> simp_all only [embedding, FourPathNaturality.replace, id_eq]

theorem projection_eq {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    projection path = embedTrack (expandTrack path) := by
  induction path <;> simp_all only [projection, FourPathNaturality.replace, image, expandTrack, embedTrack, id_eq]

theorem image_support {a b} {p q : Circuit signature a b} (change : Step rules p q) :
    RewriteTrack.support (image change) = change.support := by
  rw [image, embedTrack_support, expandStep_support]

theorem embedding_support {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    RewriteTrack.support (embedding path) = path.support := congrArg RewriteTrack.support (embedding_eq path)

theorem projection_support {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    RewriteTrack.support (projection path) = path.support :=
  (congrArg RewriteTrack.support (projection_eq path)).trans ((embedTrack_support _).trans (expandTrack_support path))

def stepSquare {a b} {p q : Circuit signature a b} (change : Step rules p q) :
    Cell (.comp (.step change) (.refl q)) (.comp (.refl p) (image change)) :=
  (Four.rightUnit (.step change)).trans
    ((eliminateStep change).cell.trans (Four.leftUnit (image change)).symm)

theorem stepSquare_support {a b} {p q : Circuit signature a b} (change : Step rules p q) :
    PresentedCell.support (stepSquare change) = change.support := by
  simp only [stepSquare, PresentedCell.support, RewriteTrack.support, (eliminateStep change).support_eq,
    embedTrack_support, expandStep_support, Finset.union_self]

def rawSquare {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    Cell (.comp (embedding path) (.refl q)) (.comp (.refl p) (projection path)) :=
  FourPathNaturality.natural id id (fun change => .step change) (fun change => image change)
    (fun circuit => .refl circuit) (fun change => stepSquare change) path

theorem rawSquare_support {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    PresentedCell.support (rawSquare path) = path.support := by
  change PresentedCell.support (FourPathNaturality.natural id id (fun change => .step change)
    (fun change => image change) (fun circuit => .refl circuit) (fun change => stepSquare change) path) = _
  have result := PresentedPathNaturality.natural_support (basis := basis) (sourceRules := rules)
    id id (fun change => .step change) (fun change => image change) (fun circuit => .refl circuit)
    (fun change => stepSquare change) ∅
    (fun track => by
      change RewriteTrack.support (embedding track) ⊆ _
      exact (embedding_support track).le.trans Finset.subset_union_left)
    (fun track => by
      change RewriteTrack.support (projection track) ⊆ _
      exact (projection_support track).le.trans Finset.subset_union_left)
    (fun circuit => by simp only [RewriteTrack.support, Finset.union_empty, id_eq])
    (fun change => (stepSquare_support change).trans (Finset.union_empty _).symm) path
  exact result.trans (Finset.union_empty _)

def comparison {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    { cell : Cell path (embedTrack (expandTrack path)) // PresentedCell.support cell = path.support } := by
  let stripped : Cell (embedding path) (projection path) :=
    (Four.rightUnit (embedding path)).symm.trans ((rawSquare path).trans (Four.leftUnit (projection path)))
  have supported : PresentedCell.support stripped = path.support := by
    simp only [stripped, PresentedCell.support, embedding_support,
      rawSquare_support, projection_support, Finset.union_self]
  let both : { cell : Cell (embedding path) (projection path) // PresentedCell.support cell = path.support } :=
    ⟨stripped, supported⟩
  let leftFamily (edge : RewriteTrack (relators := rules) p q) :=
    { cell : Cell edge (projection path) // PresentedCell.support cell = path.support }
  let first := cast (congrArg leftFamily (embedding_eq path)) both
  let rightFamily (edge : RewriteTrack (relators := rules) p q) :=
    { cell : Cell path edge // PresentedCell.support cell = path.support }
  exact cast (congrArg rightFamily (projection_eq path)) first

def edgeCount {a b : Port signature} : {p q : Circuit signature a b} → RewriteTrack (relators := rules) p q → Nat
  | _, _, .refl _ => 0
  | _, _, .step _ => 1
  | _, _, .comp first second => edgeCount first + edgeCount second
  | _, _, .inv child => edgeCount child

theorem suffix_image_edges {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    edgeCount (image (suffixStep p q tail)) = 2 := rfl

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion.PathResidual
