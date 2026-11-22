import tmp.sheaf.n8.closure.EtaNormalizedHaarTransportActual2
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import Mathlib

/-!
# Explicit ContinuousAddEquiv record, actual construction

Combines the actual completion homeomorphism with the actual ring equivalence by
proving their functions agree on values, then uses the homeomorphism equivalence
as the underlying equivalence.  This gives the record needed for
Measure.map/AddEquiv.isAddHaarMeasure_map, with no arbitrary transport.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual2

namespace LeanFormal.IUT.N8Closure.EtaContinuousAddEquivRecordActual2

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The homeomorphism and the ring equivalence agree on every value. -/
theorem homeomorph_apply_eq_ringEquiv
    (x : EtaRssAdmissibleCorrection.K X) :
    (qoCompletionHomeomorph X) x = (qoCompletionRingEquiv X) x := by
  simp only [qoCompletionHomeomorph, commonPrimeCompletionActualHomeomorph,
    qoCompletionRingEquiv, normalizedCompletionRingEquiv]
  change (normalizedCompletionHomeomorph (nativeFPlaceOverBad X)) x =
    (normalizedCompletionRingEquiv (nativeFPlaceOverBad X)) x
  rw [normalizedCompletionHomeomorph_apply]

/-- Explicit continuous additive equivalence using the actual homeomorphism
equivalence and the additive law from the ring equivalence. -/
def qoContinuousAddEquiv :
    EtaRssAdmissibleCorrection.K X ≃ₜ+ QCompletion X where
  toEquiv := (qoCompletionHomeomorph X).toEquiv
  map_add' := by
    intro x y
    calc (qoCompletionHomeomorph X) (x + y)
        = (qoCompletionRingEquiv X) (x + y) := homeomorph_apply_eq_ringEquiv X (x + y)
      _ = (qoCompletionRingEquiv X) x + (qoCompletionRingEquiv X) y := map_add _ _ _
      _ = (qoCompletionHomeomorph X) x + (qoCompletionHomeomorph X) y := by
        rw [homeomorph_apply_eq_ringEquiv X x, homeomorph_apply_eq_ringEquiv X y]
  continuous_toFun := (qoCompletionHomeomorph X).continuous
  continuous_invFun := (qoCompletionHomeomorph X).symm.continuous

/-- The required instanceable record is actual. -/
theorem qoContinuousAddEquiv_actual :
    Nonempty (EtaRssAdmissibleCorrection.K X ≃ₜ+ QCompletion X) :=
  ⟨qoContinuousAddEquiv X⟩


variable [MeasurableSpace (EtaRssAdmissibleCorrection.K X)] [BorelSpace (EtaRssAdmissibleCorrection.K X)]
variable [ProperSpace (EtaRssAdmissibleCorrection.K X)] [IsUltrametricDist (EtaRssAdmissibleCorrection.K X)]
variable [LocallyCompactSpace (EtaRssAdmissibleCorrection.K X)]
variable [NormedSpace ℚ_[FPlacePrime X] (EtaRssAdmissibleCorrection.K X)]
variable [FiniteDimensional ℚ_[FPlacePrime X] (EtaRssAdmissibleCorrection.K X)]
variable [Nontrivial (EtaRssAdmissibleCorrection.K X)]
variable [NormSMulClass ℚ_[FPlacePrime X] (EtaRssAdmissibleCorrection.K X)]
variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

/-- Canonical integral ball at K. -/
def O_K : Set (EtaRssAdmissibleCorrection.K X) :=
  LeanFormal.IUT.LocalFieldIntegralUnits.Integers (EtaRssAdmissibleCorrection.K X)

/-- Canonical integral ball at QCompletion. -/
def O_Q : Set (QCompletion X) :=
  LeanFormal.IUT.LocalFieldIntegralUnits.Integers (QCompletion X)

/-- Actual Haar mass of O_K. -/
def massK : ENNReal :=
  (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (EtaRssAdmissibleCorrection.K X)) (O_K X)

/-- Actual normalized Haar on K. -/
def μK : MeasureTheory.Measure (EtaRssAdmissibleCorrection.K X) :=
  (massK X)⁻¹ • (MeasureTheory.Measure.addHaar :
    MeasureTheory.Measure (EtaRssAdmissibleCorrection.K X))

theorem μK_O_K : μK X (O_K X) = 1 := by
  have hm := LeanFormal.IUT.LocalFieldLogarithm.measure_localIntegers_pos_lt_top
    (K := EtaRssAdmissibleCorrection.K X)
    (μ := (MeasureTheory.Measure.addHaar :
      MeasureTheory.Measure (EtaRssAdmissibleCorrection.K X)))
  simp [μK, massK, O_K, ENNReal.inv_mul_cancel hm.1.ne' hm.2.ne]

/-- Pushforward of the actual normalized Haar to QCompletion along the explicit
ContinuousAddEquiv. -/
def pushed : MeasureTheory.Measure (QCompletion X) :=
  MeasureTheory.Measure.map (qoContinuousAddEquiv X) (μK X)

/-- The pushforward is additive Haar (actual record used). -/
theorem pushed_isHaar : (pushed X).IsAddHaarMeasure := by
  have hm := LeanFormal.IUT.LocalFieldLogarithm.measure_localIntegers_pos_lt_top
    (K := EtaRssAdmissibleCorrection.K X)
    (μ := (MeasureTheory.Measure.addHaar :
      MeasureTheory.Measure (EtaRssAdmissibleCorrection.K X)))
  haveI : (μK X).IsAddHaarMeasure := by
    rw [μK]
    exact MeasureTheory.Measure.IsAddHaarMeasure.smul _
      (ENNReal.inv_ne_zero.mpr hm.2.ne) (ENNReal.inv_ne_top.mpr hm.1.ne')
  exact (qoContinuousAddEquiv X).isAddHaarMeasure_map (μK X)

/-- Exact remaining normalization target for the pushforward. -/
def PushedNormalizedAtOQ : Prop := (pushed X) (O_Q X) = 1

end LeanFormal.IUT.N8Closure.EtaContinuousAddEquivRecordActual2
