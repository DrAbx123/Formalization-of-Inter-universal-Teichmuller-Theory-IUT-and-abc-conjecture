import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceGaloisLogShell
import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitLogarithmRationalization

/-!
# Actual arithmetic algebraic unit perfection and its Galois invariants

The localized original integer units identify with the actual algebraic
closure by their logarithm. The absolute Galois action agrees on original
unit generators. Its fixed part is the embedded completion, whereas the
scaled logarithmic image of the fixed original units remains the compact
shell previously constructed. These two objects are kept distinct.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

abbrev SourceUnitPerfection (place : NumberField.FinitePlace K) :=
  UnitLogPerfection (SourceAlgebraicClosure place)

def sourceUnitPerfectionEquiv (place : NumberField.FinitePlace K) :
    SourceUnitPerfection place ≃ₗ[ℚ] SourceAlgebraicClosure place :=
  algebraicUnitPerfectionEquiv (p := (completionRationalPrime place).val)

theorem sourceUnitPerfectionEquiv_mk_one (place : NumberField.FinitePlace K)
    (u : (Integers (SourceAlgebraicClosure place))ˣ) :
    sourceUnitPerfectionEquiv place (LocalizedModule.mk (Additive.ofMul u) 1) =
      algebraicUnitLog (p := (completionRationalPrime place).val) u :=
  algebraicUnitPerfectionEquiv_mk_one u

abbrev sourceUnitPerfectionGaloisAction (place : NumberField.FinitePlace K) :
    MulAction (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place) (SourceUnitPerfection place) where
  smul σ x := (sourceUnitPerfectionEquiv place).symm (σ (sourceUnitPerfectionEquiv place x))
  one_smul x := (sourceUnitPerfectionEquiv place).symm_apply_apply x
  mul_smul σ τ x := by
    change (sourceUnitPerfectionEquiv place).symm ((σ * τ) (sourceUnitPerfectionEquiv place x)) =
      (sourceUnitPerfectionEquiv place).symm (σ (sourceUnitPerfectionEquiv place
        ((sourceUnitPerfectionEquiv place).symm (τ (sourceUnitPerfectionEquiv place x)))))
    rw [LinearEquiv.apply_symm_apply]
    rfl

theorem sourceUnitPerfectionEquiv_galois_smul (place : NumberField.FinitePlace K)
    (σ : SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place) (x : SourceUnitPerfection place) :
    letI := sourceUnitPerfectionGaloisAction place
    sourceUnitPerfectionEquiv place (σ • x) = σ (sourceUnitPerfectionEquiv place x) :=
  (sourceUnitPerfectionEquiv place).apply_symm_apply _

theorem sourceUnitPerfection_mk_galois_smul (place : NumberField.FinitePlace K)
    (σ : SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place) (u : (Integers (SourceAlgebraicClosure place))ˣ) :
    letI := sourceUnitPerfectionGaloisAction place
    σ • (LocalizedModule.mk (Additive.ofMul u) 1 : SourceUnitPerfection place) =
      LocalizedModule.mk (Additive.ofMul
        (localGaloisUnitMap (σ.restrictScalars (PadicScalarField place)) u)) 1 := by
  letI := sourceUnitPerfectionGaloisAction place
  apply (sourceUnitPerfectionEquiv place).injective
  rw [sourceUnitPerfectionEquiv_galois_smul,
    sourceUnitPerfectionEquiv_mk_one, sourceUnitPerfectionEquiv_mk_one]
  exact (algebraicUnitLog_localGalois_smul
    (σ.restrictScalars (PadicScalarField place)) u).symm

theorem sourceUnitPerfection_fixed_iff (place : NumberField.FinitePlace K)
    (x : SourceUnitPerfection place) :
    letI := sourceUnitPerfectionGaloisAction place
    (∀ σ : SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place, σ • x = x) ↔
      sourceUnitPerfectionEquiv place x ∈
        Set.range (algebraMap (NormalizedCompletion place) (SourceAlgebraicClosure place)) := by
  letI := sourceUnitPerfectionGaloisAction place
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  constructor
  · intro hx σ
    rw [← sourceUnitPerfectionEquiv_galois_smul, hx σ]
  · intro hx σ
    apply (sourceUnitPerfectionEquiv place).injective
    rw [sourceUnitPerfectionEquiv_galois_smul, hx σ]

theorem sourceGaloisFixedUnitLog_eq_algebraicUnitLog (place : NumberField.FinitePlace K)
    (u : SourceGaloisFixedUnits place) :
    sourceGaloisFixedUnitLog place u =
      algebraicUnitLog (p := (completionRationalPrime place).val) u.val := by
  let v := (baseUnitsGaloisFixedEquiv (K := NormalizedCompletion place)
    (L := SourceAlgebraicClosure place) (p := (completionRationalPrime place).val)).symm u
  let he := isometry_localField_algebraMap (K := NormalizedCompletion place)
    (L := SourceAlgebraicClosure place)
  have hu : integralUnitMap
      (algebraMap (NormalizedCompletion place) (SourceAlgebraicClosure place)) he v = u.val :=
    congrArg Subtype.val ((baseUnitsGaloisFixedEquiv
      (p := (completionRationalPrime place).val)).apply_symm_apply u)
  change algebraMap (NormalizedCompletion place) (SourceAlgebraicClosure place) (unitLog v) = _
  rw [← hu, algebraicUnitLog_eq_map (p := (completionRationalPrime place).val)]

theorem sourceGaloisLogShell_eq_algebraicUnitLog_range (place : NumberField.FinitePlace K) :
    (sourceGaloisLogShell place : Set (SourceAlgebraicClosure place)) =
      Set.range (fun u : SourceGaloisFixedUnits place =>
        (logShellScale (completionRationalPrime place).val : SourceAlgebraicClosure place)⁻¹ *
          algebraicUnitLog (p := (completionRationalPrime place).val) u.val) := by
  rw [sourceGaloisLogShell_eq_fixedUnitLog_range]
  congr 1
  funext u
  rw [sourceGaloisFixedUnitLog_eq_algebraicUnitLog]

end

end LeanFormal.IUT.NumberFieldFinitePlace
