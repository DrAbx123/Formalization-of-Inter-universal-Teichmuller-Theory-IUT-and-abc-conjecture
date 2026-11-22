import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import LeanFormal.IUT.Foundations.LocalFields.GaloisFixedUnitLogarithm

/-!
# The actual Galois-fixed pre-log-shell

The original units fixed by Gal(Kbar_v/K_v) descend to O_v units.
Their logarithmic image in the actual algebraic closure is precisely the
embedded completion logarithmic image. Scaling gives the compact shell
of III Definition 1.1; no completeness of the algebraic closure is used.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def completionToSourceAlgebraicClosure (place : NumberField.FinitePlace K) :
    Completion place →+* SourceAlgebraicClosure place :=
  (algebraMap (NormalizedCompletion place) (SourceAlgebraicClosure place)).comp
    (normalizedCompletionRingEquiv place).symm.toRingHom

theorem continuous_completionToSourceAlgebraicClosure (place : NumberField.FinitePlace K) :
    Continuous (completionToSourceAlgebraicClosure place) :=
  (isometry_localField_algebraMap (K := NormalizedCompletion place)
    (L := SourceAlgebraicClosure place)).continuous.comp
      (normalizedCompletionHomeomorph place).symm.continuous

abbrev SourceGaloisFixedUnits (place : NumberField.FinitePlace K) :=
  localGaloisFixedIntegralUnits (K := NormalizedCompletion place)
    (L := SourceAlgebraicClosure place) (p := (completionRationalPrime place).val)

def sourceGaloisFixedUnitLog (place : NumberField.FinitePlace K)
    (u : SourceGaloisFixedUnits place) : SourceAlgebraicClosure place :=
  galoisFixedUnitLog (p := (completionRationalPrime place).val) u

def sourceGaloisLogShell (place : NumberField.FinitePlace K) :
    AddSubgroup (SourceAlgebraicClosure place) :=
  galoisFixedLogShell (K := NormalizedCompletion place)
    (L := SourceAlgebraicClosure place) (p := (completionRationalPrime place).val)

theorem sourceGaloisLogShell_eq_fixedUnitLog_range (place : NumberField.FinitePlace K) :
    (sourceGaloisLogShell place : Set (SourceAlgebraicClosure place)) =
      Set.range (fun u : SourceGaloisFixedUnits place =>
        (logShellScale (completionRationalPrime place).val : SourceAlgebraicClosure place)⁻¹ *
          sourceGaloisFixedUnitLog place u) :=
  galoisFixedLogShell_eq_fixedUnitLog_range

theorem sourceGaloisFixedUnitLog_eq_log1p (place : NumberField.FinitePlace K)
    (u : SourceGaloisFixedUnits place)
    (hu : ‖(u.val.val : SourceAlgebraicClosure place) - 1‖ < 1) :
    sourceGaloisFixedUnitLog place u =
      log1p ((u.val.val : SourceAlgebraicClosure place) - 1) :=
  galoisFixedUnitLog_eq_log1p u hu

theorem sourceGaloisLogShell_eq_completion_image (place : NumberField.FinitePlace K) :
    (sourceGaloisLogShell place : Set (SourceAlgebraicClosure place)) =
      completionToSourceAlgebraicClosure place ''
        (completionLogShell place : Set (Completion place)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨normalizedCompletionRingEquiv place y, ⟨y, hy, rfl⟩, ?_⟩
    change algebraMap (NormalizedCompletion place) (SourceAlgebraicClosure place)
      ((normalizedCompletionRingEquiv place).symm
        (normalizedCompletionRingEquiv place y)) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    change algebraMap (NormalizedCompletion place) (SourceAlgebraicClosure place) y =
      algebraMap (NormalizedCompletion place) (SourceAlgebraicClosure place)
        ((normalizedCompletionRingEquiv place).symm
          (normalizedCompletionRingEquiv place y))
    rw [RingEquiv.symm_apply_apply]

theorem isCompact_sourceGaloisLogShell (place : NumberField.FinitePlace K) :
    IsCompact (sourceGaloisLogShell place : Set (SourceAlgebraicClosure place)) :=
  isCompact_galoisFixedLogShell

theorem completionIntegers_image_subset_sourceGaloisLogShell
    (place : NumberField.FinitePlace K) :
    completionToSourceAlgebraicClosure place ''
      (CompletionIntegers place : Set (Completion place)) ⊆ sourceGaloisLogShell place := by
  rw [sourceGaloisLogShell_eq_completion_image]
  exact Set.image_mono (completionIntegers_subset_logShell place)

theorem sourceGaloisLogShell_fixed (place : NumberField.FinitePlace K)
    (σ : SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place)
    {x : SourceAlgebraicClosure place} (hx : x ∈ sourceGaloisLogShell place) : σ x = x := by
  obtain ⟨y, _, rfl⟩ := hx
  exact σ.commutes y

end

end LeanFormal.IUT.NumberFieldFinitePlace
