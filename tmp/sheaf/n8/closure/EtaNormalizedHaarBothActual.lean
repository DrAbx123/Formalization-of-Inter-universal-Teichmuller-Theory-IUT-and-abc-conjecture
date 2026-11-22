import tmp.sheaf.n8.closure.EtaQOReadoutRelationActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import Mathlib

/-!
# Actual normalized Haar measures at both F carriers

Instead of assuming normalization inputs, define

  muK := (massK)^-1 • addHaar on K,
  muQ := (massQ)^-1 • addHaar on QCompletion,

where massK/massQ are the actual Haar masses of the integral-unit balls.  The
production theorem measure_localIntegers_pos_lt_top gives positivity and
finiteness, hence muK(O_K)=1 and muQ(O_Q)=1 actually.  The remaining
common-carrier measure transport (K vs QCompletion) is recorded as a separate
exact gap.  No arbitrary normalization is assumed.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaGlobalRssAtF
open LeanFormal.IUT.N8Closure.EtaQOClassGlobalActual

namespace LeanFormal.IUT.N8Closure.EtaNormalizedHaarBothActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (EtaRssAdmissibleCorrection.K X)] [BorelSpace (EtaRssAdmissibleCorrection.K X)]
variable [ProperSpace (EtaRssAdmissibleCorrection.K X)] [IsUltrametricDist (EtaRssAdmissibleCorrection.K X)]
variable [LocallyCompactSpace (EtaRssAdmissibleCorrection.K X)]
variable [NormedSpace ℚ_[FPlacePrime X] (EtaRssAdmissibleCorrection.K X)]
variable [FiniteDimensional ℚ_[FPlacePrime X] (EtaRssAdmissibleCorrection.K X)]
variable [Nontrivial (EtaRssAdmissibleCorrection.K X)]
variable [NormSMulClass ℚ_[FPlacePrime X] (EtaRssAdmissibleCorrection.K X)]

/-- Canonical integral-unit ball at K. -/
def O_K : Set (EtaRssAdmissibleCorrection.K X) := Integers (EtaRssAdmissibleCorrection.K X)

/-- Actual Haar mass of O_K for the canonical additive Haar measure. -/
def massK : ENNReal := (Measure.addHaar : Measure (EtaRssAdmissibleCorrection.K X)) (O_K X)

/-- Normalized Haar measure on K: divide by the actual mass of O_K. -/
def μK : Measure (EtaRssAdmissibleCorrection.K X) := (massK X)⁻¹ • (Measure.addHaar : Measure (EtaRssAdmissibleCorrection.K X))

/-- muK is actually normalized at O_K. -/
theorem μK_O_K : μK X (O_K X) = 1 := by
  have hm := measure_localIntegers_pos_lt_top (K := EtaRssAdmissibleCorrection.K X)
    (μ := (Measure.addHaar : Measure (EtaRssAdmissibleCorrection.K X)))
  simp [μK, massK, O_K, ENNReal.inv_mul_cancel hm.1.ne' hm.2.ne]

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

/-- Canonical integral-unit ball at QCompletion. -/
def O_Q : Set (QCompletion X) := Integers (QCompletion X)

/-- Actual Haar mass of O_Q. -/
def massQ : ENNReal := (Measure.addHaar : Measure (QCompletion X)) (O_Q X)

/-- Normalized Haar measure on QCompletion. -/
def μQ : Measure (QCompletion X) :=
  (massQ X)⁻¹ • (Measure.addHaar : Measure (QCompletion X))

/-- muQ is actually normalized at O_Q. -/
theorem μQ_O_Q : μQ X (O_Q X) = 1 := by
  have hm := measure_localIntegers_pos_lt_top (K := QCompletion X)
    (μ := (Measure.addHaar : Measure (QCompletion X)))
  simp [μQ, massQ, O_Q, ENNReal.inv_mul_cancel hm.1.ne' hm.2.ne]

/-- Both normalized masses are nonzero and finite (used to identify scalar
factors). -/
theorem massK_pos_lt_top : 0 < massK X ∧ massK X < ⊤ := by
  have hm := measure_localIntegers_pos_lt_top (K := EtaRssAdmissibleCorrection.K X)
    (μ := (Measure.addHaar : Measure (EtaRssAdmissibleCorrection.K X)))
  exact ⟨by simpa [massK, O_K] using hm.1, by simpa [massK, O_K] using hm.2⟩

theorem massQ_pos_lt_top : 0 < massQ X ∧ massQ X < ⊤ := by
  have hm := measure_localIntegers_pos_lt_top (K := QCompletion X)
    (μ := (Measure.addHaar : Measure (QCompletion X)))
  exact ⟨by simpa [massQ, O_Q] using hm.1, by simpa [massQ, O_Q] using hm.2⟩

/-- Exact remaining transport: identify the normalized Haar measure on
QCompletion with the normalized Haar measure on K along the carrier equality.
No arbitrary transport is chosen. -/
def NormalizedHaarCarrierTransport : Prop :=
  Nonempty ({ μ' : Measure (EtaRssAdmissibleCorrection.K X) // μ' = μK X } ≃ { μ' : Measure (QCompletion X) // μ' = μQ X })

/-- Direct corollary of the previously proved normalized-Haar agreement:
normalized measures agree on every everywhere-positive measurable set. -/
theorem normalized_haar_readout_agree
    {G : Type u} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (mu' mu : Measure G) [mu.IsAddHaarMeasure] [mu'.IsAddHaarMeasure]
    {O : Set G} (hO : IsOpen O) (hmuO : mu O = 1) (hmu'O : mu' O = 1)
    {s : Set G} (hs : MeasurableSet s) (hpos : mu.IsEverywherePos s) :
    mu' s = mu s :=
  EtaQOReadoutRelationActual.normalized_haar_agree_on_everywherePos
    mu' mu hO hmuO hmu'O hs hpos

end LeanFormal.IUT.N8Closure.EtaNormalizedHaarBothActual
