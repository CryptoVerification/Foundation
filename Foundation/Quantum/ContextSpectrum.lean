import Foundation.Quantum.Contexts
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Topology.Sets.Opens

/-! Actual character spectra of closed commuting contexts. These are the
local ingredients of the external spectrum; they do not themselves identify
the internal locale or prove the Kochen–Specker obstruction. -/
namespace Foundation.Quantum.Bohr
noncomputable section
set_option backward.isDefEq.respectTransparency false
open WeakDual
variable {A : Type} [CStarAlgebra A]

instance Context.closedInstance (C : Context A) : IsClosed (C.algebra : Set A) := C.closed

instance Context.commCStarAlgebra (C : Context A) : CommCStarAlgebra C.algebra where
  toCStarAlgebra := StarSubalgebra.cstarAlgebra C.algebra
  mul_comm := C.commutative

abbrev Context.Spectrum (C : Context A) := characterSpace ℂ C.algebra

def Context.inclusion {C D : Context A} (h : C ≤ D) : C.algebra →⋆ₐ[ℂ] D.algebra :=
  StarSubalgebra.inclusion h

/-- Characters restrict contravariantly along actual inclusions of observations. -/
def Context.restrict {C D : Context A} (h : C ≤ D) : C(D.Spectrum, C.Spectrum) :=
  CharacterSpace.compContinuousMap (Context.inclusion h)

@[simp] theorem Context.restrict_id (C : Context A) :
    Context.restrict (le_refl C) = ContinuousMap.id C.Spectrum := by
  exact CharacterSpace.compContinuousMap_id C.algebra

theorem Context.restrict_comp {C D E : Context A} (h : C ≤ D) (k : D ≤ E) :
    Context.restrict (h.trans k) = (Context.restrict h).comp (Context.restrict k) := by
  exact CharacterSpace.compContinuousMap_comp (Context.inclusion k) (Context.inclusion h)

/-- The local Gelfand representation is an equivalence, not an assumed interpretation. -/
def Context.gelfand (C : Context A) : C.algebra ≃⋆ₐ[ℂ] C(C.Spectrum, ℂ) :=
  gelfandStarTransform C.algebra

theorem Context.gelfand_naturality {C D : Context A} (h : C ≤ D) :
    (D.gelfand : _ →⋆ₐ[ℂ] _).comp (Context.inclusion h) =
      ((Context.restrict h).compStarAlgHom' ℂ ℂ).comp (C.gelfand : _ →⋆ₐ[ℂ] _) :=
  gelfandStarTransform_naturality (Context.inclusion h)

/-- Spectral opens transport covariantly by continuous preimage. -/
def Context.transportOpen {C D : Context A} (h : C ≤ D)
    (U : TopologicalSpace.Opens C.Spectrum) : TopologicalSpace.Opens D.Spectrum :=
  TopologicalSpace.Opens.comap (Context.restrict h) U

@[simp] theorem Context.transportOpen_id (C : Context A)
    (U : TopologicalSpace.Opens C.Spectrum) : Context.transportOpen (le_refl C) U = U := by
  ext x
  rfl

theorem Context.transportOpen_comp {C D E : Context A} (h : C ≤ D) (k : D ≤ E)
    (U : TopologicalSpace.Opens C.Spectrum) :
    Context.transportOpen (h.trans k) U = Context.transportOpen k (Context.transportOpen h U) := by
  ext x
  rfl

/-- The positive spectral generator associated with an actual observable. -/
def Context.positiveOpen (C : Context A) (a : C.algebra) : TopologicalSpace.Opens C.Spectrum :=
  ⟨{χ | 0 < (χ a).re}, isOpen_lt continuous_const
    (Complex.continuous_re.comp (map_continuous (gelfandTransform ℂ C.algebra a)))⟩

@[simp] theorem Context.positiveOpen_zero (C : Context A) : C.positiveOpen 0 = ⊥ := by
  ext χ
  simp [Context.positiveOpen]

@[simp] theorem Context.positiveOpen_one (C : Context A) : C.positiveOpen 1 = ⊤ := by
  ext χ
  simp [Context.positiveOpen]

/-- The generator for an observation is preserved by changing its available context. -/
theorem Context.transport_positiveOpen {C D : Context A} (h : C ≤ D) (a : C.algebra) :
    Context.transportOpen h (C.positiveOpen a) =
      D.positiveOpen (Context.inclusion h a) := by
  ext χ
  rfl

/-- The external space of local spectral points; opens must persist along restriction. -/
abbrev SpectrumBundle (A : Type) [CStarAlgebra A] := (C : Context A) × C.Spectrum

instance spectrumBundleTopology : TopologicalSpace (SpectrumBundle A) where
  IsOpen U :=
    (∀ C : Context A, IsOpen ((fun x : C.Spectrum => (⟨C, x⟩ : SpectrumBundle A)) ⁻¹' U)) ∧
    (∀ (C D : Context A) (h : C ≤ D) (x : D.Spectrum),
      (⟨C, Context.restrict h x⟩ : SpectrumBundle A) ∈ U → ⟨D, x⟩ ∈ U)
  isOpen_univ := ⟨fun _ => isOpen_univ, fun _ _ _ _ _ => Set.mem_univ _⟩
  isOpen_inter U V hU hV := ⟨fun C => (hU.1 C).inter (hV.1 C),
    fun C D h x hx => ⟨hU.2 C D h x hx.1, hV.2 C D h x hx.2⟩⟩
  isOpen_sUnion S hS := ⟨by
    intro C
    rw [Set.preimage_sUnion]
    exact isOpen_biUnion (fun U hU => (hS U hU).1 C), by
    intro C D h x hx
    obtain ⟨U, hU, hx⟩ := Set.mem_sUnion.mp hx
    exact Set.mem_sUnion.mpr ⟨U, hU, (hS U hU).2 C D h x hx⟩⟩

/-- A frame of genuine spectral propositions, not just availability of an observation. -/
abbrev SpectralOpen (A : Type) [CStarAlgebra A] := TopologicalSpace.Opens (SpectrumBundle A)

/-- Local spectral truth is open in every ordinary Gelfand spectrum. -/
def SpectralOpen.fiber (U : SpectralOpen A) (C : Context A) :
    TopologicalSpace.Opens C.Spectrum :=
  ⟨(fun x : C.Spectrum => (⟨C, x⟩ : SpectrumBundle A)) ⁻¹' (U : Set (SpectrumBundle A)),
    U.isOpen.1 C⟩

theorem SpectralOpen.persistent (U : SpectralOpen A) {C D : Context A} (h : C ≤ D) :
    Context.transportOpen h (U.fiber C) ≤ U.fiber D :=
  fun x hx => U.isOpen.2 C D h x hx


end
end Foundation.Quantum.Bohr
