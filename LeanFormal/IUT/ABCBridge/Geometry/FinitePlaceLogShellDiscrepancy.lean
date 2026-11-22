import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex

/-!
# Actual finite-place log-shell discrepancy

The finite index is constructed on the actual normalized completion. The
proved homeomorphism and integer-ring identification transport the Haar
formula to the existing completionLogShell on the original completion.
Thus this is an exact volume formula for the actual source shell.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm MeasureTheory

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def completionLogShellIntegerIndex (place : NumberField.FinitePlace K) : ℕ :=
  logShellIntegerIndex (K := NormalizedCompletion place) (p := (completionRationalPrime place).val)

def completionLogShellDiscrepancy (place : NumberField.FinitePlace K) : ℝ :=
  integralLogShellDiscrepancy (K := NormalizedCompletion place)
    (p := (completionRationalPrime place).val)

theorem completionLogShellIntegerIndex_pos (place : NumberField.FinitePlace K) :
    0 < completionLogShellIntegerIndex place :=
  logShellIntegerIndex_pos (K := NormalizedCompletion place)
    (p := (completionRationalPrime place).val)

theorem completionLogShellDiscrepancy_nonneg (place : NumberField.FinitePlace K) :
    0 ≤ completionLogShellDiscrepancy place :=
  integralLogShellDiscrepancy_nonneg (K := NormalizedCompletion place)
    (p := (completionRationalPrime place).val)

theorem normalizedCompletionRingEquiv_image_logShell (place : NumberField.FinitePlace K) :
    normalizedCompletionRingEquiv place ''
      (integralLogShell (K := NormalizedCompletion place)
        (p := (completionRationalPrime place).val) : Set (NormalizedCompletion place)) =
      (completionLogShell place : Set (Completion place)) := rfl

theorem normalizedCompletionRingEquiv_image_integers (place : NumberField.FinitePlace K) :
    normalizedCompletionRingEquiv place '' (Integers (NormalizedCompletion place) : Set _) =
      (CompletionIntegers place : Set (Completion place)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_completionIntegers_iff_norm_le_one place _).mpr
      ((normalizedCompletion_norm_le_one_iff place _).mpr ((mem_integers_iff _).mp hy))
  · intro hx
    have hy : (normalizedCompletionRingEquiv place).symm x ∈
        Integers (NormalizedCompletion place) := by
      apply (mem_integers_iff _).mpr
      apply (normalizedCompletion_norm_le_one_iff place _).mp
      simpa only [RingEquiv.apply_symm_apply] using
        (mem_completionIntegers_iff_norm_le_one place _).mp hx
    exact ⟨(normalizedCompletionRingEquiv place).symm x, hy,
      (normalizedCompletionRingEquiv place).apply_symm_apply x⟩

theorem completionLogShell_measure_eq_index_mul (place : NumberField.FinitePlace K)
    [MeasurableSpace (Completion place)] [BorelSpace (Completion place)]
    (μ : Measure (Completion place)) [Measure.IsAddHaarMeasure μ] :
    μ (completionLogShell place : Set (Completion place)) =
      (completionLogShellIntegerIndex place : ENNReal) * μ (CompletionIntegers place : Set _) := by
  letI : MeasurableSpace (NormalizedCompletion place) := borel _
  letI : BorelSpace (NormalizedCompletion place) := ⟨rfl⟩
  let embedding := (normalizedCompletionRingEquiv place).toAddMonoidHom
  have hopen : Topology.IsOpenEmbedding embedding :=
    (normalizedCompletionHomeomorph place).isOpenEmbedding
  let normalizedMeasure := μ.comap embedding
  letI : Measure.IsAddHaarMeasure normalizedMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ hopen
  have hmass := measure_integralLogShell_eq_index_mul
    (p := (completionRationalPrime place).val) normalizedMeasure
  have hcomap (S : Set (NormalizedCompletion place)) :
      normalizedMeasure S = μ (normalizedCompletionRingEquiv place '' S) :=
    hopen.measurableEmbedding.comap_apply μ S
  simpa only [hcomap, normalizedCompletionRingEquiv_image_logShell,
    normalizedCompletionRingEquiv_image_integers, completionLogShellIntegerIndex] using hmass

theorem completionLogShellDiscrepancy_eq_relativeHaarLog (place : NumberField.FinitePlace K)
    [MeasurableSpace (Completion place)] [BorelSpace (Completion place)]
    (μ : Measure (Completion place)) [Measure.IsAddHaarMeasure μ] :
    completionLogShellDiscrepancy place =
      Real.log (μ (completionLogShell place : Set (Completion place))).toReal -
        Real.log (μ (CompletionIntegers place : Set (Completion place))).toReal := by
  letI : MeasurableSpace (NormalizedCompletion place) := borel _
  letI : BorelSpace (NormalizedCompletion place) := ⟨rfl⟩
  let embedding := (normalizedCompletionRingEquiv place).toAddMonoidHom
  have hopen : Topology.IsOpenEmbedding embedding :=
    (normalizedCompletionHomeomorph place).isOpenEmbedding
  let normalizedMeasure := μ.comap embedding
  letI : Measure.IsAddHaarMeasure normalizedMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ hopen
  have hlog := integralLogShellDiscrepancy_eq_relativeHaarLog
    (p := (completionRationalPrime place).val) normalizedMeasure
  have hcomap (S : Set (NormalizedCompletion place)) :
      normalizedMeasure S = μ (normalizedCompletionRingEquiv place '' S) :=
    hopen.measurableEmbedding.comap_apply μ S
  simpa only [hcomap, normalizedCompletionRingEquiv_image_logShell,
    normalizedCompletionRingEquiv_image_integers, completionLogShellDiscrepancy] using hlog

end

end LeanFormal.IUT.NumberFieldFinitePlace
