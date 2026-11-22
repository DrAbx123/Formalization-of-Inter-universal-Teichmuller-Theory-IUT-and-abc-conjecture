/-
  Consumer package for the actual infinite-place log/kernel dictionary.

  The actual local field at an infinite place v is Mathlib's completion
  `v.Completion`; the production archimedean dictionary supplies the radius,
  norm-one kernel and additive log.  This file packages those actual results
  into one consumer structure and its constructor.  It makes no source `Psi^cns`
  residual claim: only the completion-level partial carrier is exported.
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36ArchimedeanLocal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.InfinitePlaceLogKernelConsumer

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
/-- Consumer package for the actual infinite-place log/kernel dictionary. -/
structure InfinitePlaceLogConsumerData (v : NumberField.InfinitePlace F) where
  /-- The actual archimedean radius dictionary. -/
  radius : ℝ → Set (InfinitePlaceLocalField v)
  /-- Radius realization: every nonnegative radius occurs as an actual norm. -/
  radius_realization : RadiusRealization (InfinitePlaceLocalField v)
  /-- The actual norm-one kernel of the archimedean log. -/
  kernel : Subgroup (InfinitePlaceLocalField v)ˣ
  /-- The actual additive archimedean log. -/
  log : Additive (InfinitePlaceLocalField v)ˣ →+ ℝ
  /-- The kernel is exactly the norm-one subgroup. -/
  log_kernel : ∀ u : (InfinitePlaceLocalField v)ˣ,
    log (Additive.ofMul u) = 0 ↔ u ∈ kernel
  /-- The actual log is onto ℝ. -/
  log_surjective : Function.Surjective log
  /-- The exact completion-level partial `Psi^cns` carrier. -/
  psiCnsPartial : Additive (InfinitePlaceLocalField v)ˣ →+ ℝ
  /-- The partial `Psi^cns` carrier is the actual additive log. -/
  psiCnsPartial_eq_log : psiCnsPartial = log

/-- Constructor: the green `InfinitePlaceLogDictionary` material packaged as a
single actual consumer datum. -/
def infinitePlaceLogConsumer (v : NumberField.InfinitePlace F) :
    InfinitePlaceLogConsumerData v where
  radius := infinitePlaceRadius v
  radius_realization := infinitePlace_radiusRealization v
  kernel := infinitePlaceKernel v
  log := infinitePlaceLog v
  log_kernel := infinitePlaceLog_eq_zero_iff v
  log_surjective := infinitePlaceLog_surjective v
  psiCnsPartial := infinitePlacePsiCnsPartial v
  psiCnsPartial_eq_log := infinitePlacePsiCnsPartial_eq_log v

@[simp] theorem infinitePlaceLogConsumer_radius (v : NumberField.InfinitePlace F) :
    (infinitePlaceLogConsumer v).radius = infinitePlaceRadius v := rfl

@[simp] theorem infinitePlaceLogConsumer_kernel (v : NumberField.InfinitePlace F) :
    (infinitePlaceLogConsumer v).kernel = infinitePlaceKernel v := rfl

@[simp] theorem infinitePlaceLogConsumer_log (v : NumberField.InfinitePlace F) :
    (infinitePlaceLogConsumer v).log = infinitePlaceLog v := rfl

@[simp] theorem infinitePlaceLogConsumer_psiCnsPartial
    (v : NumberField.InfinitePlace F) :
    (infinitePlaceLogConsumer v).psiCnsPartial = infinitePlacePsiCnsPartial v := rfl

end LeanFormal.IUT.InfinitePlaceLogKernelConsumer

end
