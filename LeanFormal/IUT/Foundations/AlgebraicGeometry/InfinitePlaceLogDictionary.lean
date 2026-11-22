/-
  Infinite-place (archimedean) log dictionary: actual radius, kernel and partial
  `Psi^cns` carrier from the production archimedean local dictionary.

  The actual local field at an infinite place v is Mathlib's completion
  `v.Completion`; its norm is the archimedean absolute value.  The production
  dictionary supplies `localClosedBall`, `normOneUnits` and `absLogAddHom`.

  This is only the completion-level partial carrier.  The full source `Psi^cns`
  (arithmetic integral units, theta divisor and global action) is not constructed;
  the precise residual is stated at the end.
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36ArchimedeanLocal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.InfinitePlaceLogDictionary

open NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open LeanFormal.IUT

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- The actual archimedean local field at an infinite place. -/
abbrev InfinitePlaceLocalField (v : NumberField.InfinitePlace F) : Type u :=
  v.Completion

/-- The production archimedean closed ball of radius r. -/
def infinitePlaceRadius (v : NumberField.InfinitePlace F) (r : ℝ) :
    Set (InfinitePlaceLocalField v) :=
  localClosedBall (InfinitePlaceLocalField v) r

/-- The actual radius-realization property of the infinite-place completion. -/
theorem infinitePlace_radiusRealization (v : NumberField.InfinitePlace F) :
    RadiusRealization (InfinitePlaceLocalField v) := by
  intro r hr
  rcases isReal_or_isComplex v with hv | hv
  · let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
    obtain ⟨y, hy⟩ := radiusRealization_real r hr
    refine ⟨e.symm y, ?_⟩
    rw [← hy]
    have h0 : e 0 = 0 := by
      dsimp [e]
      exact (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).map_zero
    have hd := e.isometry.dist_eq (e.symm y) 0
    rw [e.apply_symm_apply, h0, dist_eq_norm, sub_zero, dist_eq_norm, sub_zero] at hd
    exact hd.symm
  · let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
    obtain ⟨y, hy⟩ := radiusRealization_complex r hr
    refine ⟨e.symm y, ?_⟩
    rw [← hy]
    have h0 : e 0 = 0 := by
      dsimp [e]
      exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).map_zero
    have hd := e.isometry.dist_eq (e.symm y) 0
    rw [e.apply_symm_apply, h0, dist_eq_norm, sub_zero, dist_eq_norm, sub_zero] at hd
    exact hd.symm

/-- The production kernel of the archimedean log: norm-one units. -/
def infinitePlaceKernel (v : NumberField.InfinitePlace F) :
    Subgroup (InfinitePlaceLocalField v)ˣ :=
  normOneUnits (InfinitePlaceLocalField v)

/-- The production additive archimedean log. -/
def infinitePlaceLog (v : NumberField.InfinitePlace F) :
    Additive (InfinitePlaceLocalField v)ˣ →+ ℝ :=
  absLogAddHom (InfinitePlaceLocalField v)

/-- Kernel description: a unit has zero log exactly when it lies in the
norm-one kernel. -/
theorem infinitePlaceLog_eq_zero_iff (v : NumberField.InfinitePlace F)
    (u : (InfinitePlaceLocalField v)ˣ) :
    infinitePlaceLog v (Additive.ofMul u) = 0 ↔
      u ∈ infinitePlaceKernel v := by
  simpa [infinitePlaceLog, infinitePlaceKernel] using
    (absLogAddHom_ofMul_eq_zero_iff (K := InfinitePlaceLocalField v) u)

/-- The actual archimedean log is onto the real line; this uses the actual
radius realization above. -/
theorem infinitePlaceLog_surjective (v : NumberField.InfinitePlace F) :
    Function.Surjective (infinitePlaceLog v) :=
  absLogAddHom_surjective (K := InfinitePlaceLocalField v)
    (infinitePlace_radiusRealization v)

/-- Partial `Psi^cns` carrier at the infinite place: the completion-level
additive log.  This is the actual partial piece; it is not the full source map. -/
def infinitePlacePsiCnsPartial (v : NumberField.InfinitePlace F) :
    Additive (InfinitePlaceLocalField v)ˣ →+ ℝ :=
  infinitePlaceLog v

theorem infinitePlacePsiCnsPartial_eq_log (v : NumberField.InfinitePlace F) :
    infinitePlacePsiCnsPartial v = infinitePlaceLog v := rfl

/-- Radius dictionary: under actual radius realization, closed balls with
nonnegative radii determine and are determined by the radius. -/
theorem infinitePlaceRadius_eq_iff (v : NumberField.InfinitePlace F)
    {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) :
    infinitePlaceRadius v r₁ = infinitePlaceRadius v r₂ ↔ r₁ = r₂ :=
  localClosedBall_eq_iff (infinitePlace_radiusRealization v) h₁ h₂

/-! ## Exact residual

ACTUAL here: at any infinite place v of a number field F, the completion
`v.Completion`, the archimedean closed-radius dictionary, the norm-one kernel,
the additive archimedean log, and its surjectivity.

NOT CONSTRUCTED: the full source `Psi^cns` carrier.  That requires the actual
source arithmetic object (integral units of the relevant cover), its theta
divisor/degree data, the global product-formula normalization and the Galois
action on the source units.  In particular this file deliberately does not
replace those by R, C, a concrete Q5 model, or an arbitrary card. -/

end LeanFormal.IUT.InfinitePlaceLogDictionary

end