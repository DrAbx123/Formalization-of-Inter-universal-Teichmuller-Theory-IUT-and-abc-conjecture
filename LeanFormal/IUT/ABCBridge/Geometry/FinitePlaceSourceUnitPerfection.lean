import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogKernel
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmRationalization
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Actual arithmetic unit perfection and its logarithmic field

The source is the localization of the actual completed integer unit group
at all nonzero integers. Transporting the proved localization property
through the actual norm/integer equivalences constructs a Q-linear
isomorphism to the project's original K_v. Its natural map is exactly the
actual logarithm and kills exactly the torsion units.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def completionUnitLogIntLinear (place : NumberField.FinitePlace K) :
    Additive (CompletionIntegers place)ˣ →ₗ[ℤ] Completion place :=
  (completionUnitLogHom place).toAdditiveLeft.toIntLinearMap

theorem completionUnitLog_isLocalizedModule (place : NumberField.FinitePlace K) :
    IsLocalizedModule (nonZeroDivisors ℤ) (completionUnitLogIntLinear place) := by
  let f := unitLogIntLinear (K := NormalizedCompletion place)
    (p := (completionRationalPrime place).val)
  letI := unitLog_isLocalizedModule (K := NormalizedCompletion place)
    (p := (completionRationalPrime place).val)
  let eSource : Additive (CompletionIntegers place)ˣ ≃ₗ[ℤ]
      Additive (LocalFieldIntegralUnits.Integers (NormalizedCompletion place))ˣ :=
    (normalizedCompletionUnitsEquiv place).symm.toAdditive.toIntLinearEquiv
  let eTarget : NormalizedCompletion place ≃ₗ[ℤ] Completion place :=
    (normalizedCompletionRingEquiv place).toAddEquiv.toIntLinearEquiv
  have hsource : IsLocalizedModule (nonZeroDivisors ℤ) (f.comp eSource.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (S := nonZeroDivisors ℤ) (f := f) eSource
  letI := hsource
  have htarget : IsLocalizedModule (nonZeroDivisors ℤ)
      (eTarget.toLinearMap.comp (f.comp eSource.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv (S := nonZeroDivisors ℤ)
      (f := f.comp eSource.toLinearMap) eTarget
  have heq : eTarget.toLinearMap.comp (f.comp eSource.toLinearMap) =
      completionUnitLogIntLinear place := by ext u; rfl
  rw [heq] at htarget
  exact htarget

/-- The concrete perfection of the actual arithmetic unit group. -/
abbrev CompletionUnitPerfection (place : NumberField.FinitePlace K) :=
  LocalizedModule (nonZeroDivisors ℤ) (Additive (CompletionIntegers place)ˣ)

instance completionUnitPerfectionRatModule (place : NumberField.FinitePlace K) :
    Module ℚ (CompletionUnitPerfection place) :=
  LocalizedModule.moduleOfIsLocalization (S := nonZeroDivisors ℤ)
    (M := Additive (CompletionIntegers place)ˣ) (T := ℚ)

def completionUnitPerfectionEquiv (place : NumberField.FinitePlace K) :
    CompletionUnitPerfection place ≃ₗ[ℚ] Completion place := by
  letI : Module ℤ (CompletionUnitPerfection place) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (CompletionIntegers place)ˣ)
  letI := completionUnitLog_isLocalizedModule place
  let e := IsLocalizedModule.iso (nonZeroDivisors ℤ) (completionUnitLogIntLinear place)
  exact { e.toAddEquiv with map_smul' := fun q x => map_rat_smul e.toAddEquiv q x }

theorem completionUnitPerfectionEquiv_mk_one (place : NumberField.FinitePlace K)
    (u : (CompletionIntegers place)ˣ) :
    completionUnitPerfectionEquiv place (LocalizedModule.mk (Additive.ofMul u) 1) =
      completionUnitLog place u := by
  letI : Module ℤ (CompletionUnitPerfection place) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (CompletionIntegers place)ˣ)
  letI := completionUnitLog_isLocalizedModule place
  change (IsLocalizedModule.iso (nonZeroDivisors ℤ) (completionUnitLogIntLinear place))
    (LocalizedModule.mk (Additive.ofMul u) 1) = completionUnitLog place u
  exact IsLocalizedModule.iso_mk_one _ _ _

theorem completionUnitPerfection_mk_eq_zero_iff_isOfFinOrder
    (place : NumberField.FinitePlace K) (u : (CompletionIntegers place)ˣ) :
    (LocalizedModule.mk (Additive.ofMul u) 1 : CompletionUnitPerfection place) = 0 ↔
      IsOfFinOrder u := by
  rw [← completionUnitLog_eq_zero_iff_isOfFinOrder place u,
    ← completionUnitPerfectionEquiv_mk_one place u]
  exact (completionUnitPerfectionEquiv place).map_eq_zero_iff.symm

end

end LeanFormal.IUT.NumberFieldFinitePlace
